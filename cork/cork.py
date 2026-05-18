#!/usr/bin/env python
#
# Cork - Authentication module for the Bottle web framework
# Copyright (C) 2012 Federico Ceratto
#
# This package is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 3 of the License, or (at your option) any later version.
#
# This package is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.
#
#
# Cork is designed for web application with a small userbase. User credentials
# are stored in a JSON file.
#
# Features:
#  - basic role support
#  - user registration
#
# Roadmap:
#  - add hooks to provide logging or user-defined functions in case of
#     login/require failure
#  - decouple authentication logic from data storage to allow multiple backends
#    (e.g. a key/value database)

from base64 import b64encode, b64decode
from beaker import crypto
from datetime import datetime, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from logging import getLogger
from smtplib import SMTP, SMTP_SSL
from threading import Thread
from time import time, time_ns
import bottle
import os
import re
import shutil
import uuid
import brotli
import json
import traceback

try:
    import json
except ImportError:  # pragma: no cover
    import simplejson as json


log = getLogger(__name__)

COUCHBASE_ENTRY_DESIGN_DOC = "admin"
COUCHBASE_ENTRY_VIEW = "keys_by_table"

class AAAException(Exception):
    """Generic Authentication/Authorization Exception"""
    pass


class AuthException(AAAException):
    """Authentication Exception: incorrect username/password pair"""
    pass

class PostgresTable(dict):
    def __init__(self, connection, postgres_table_name, table_name):
        """ Wrapper class to manage a table of postgres entries

        :param connection: postgres connection
        :type connection: psycopg2.connection
        :param table_name: the name (aka prefix) of the table entries
        :type table_name: str.
        """
        self.connection = connection
        self.postgres_table_name = postgres_table_name
        self.table_name = table_name

    def _get_entry_key(self, item):
        return "%s:%s" % (self.table_name, item)

    def _decompress(self, value):
        header = value[0]
        if header != 0:
            raise Exception("Invalid compressed object")
        return brotli.decompress(value[1:])

    def _compress(self, value):
        return b"\x00" + brotli.compress(value, quality=5)

    def _should_compress(self, value):
        return len(value) > 4096

    def _get_value_bytes(self, value):
        value_bytes = json.dumps(value).encode("utf-8")
        if self._should_compress(value_bytes):
            return True, self._compress(value_bytes)
        return False, value_bytes

    def _convert_to_value(self, value, compressed):
        if compressed:
            value = self._decompress(value)
        return json.loads(value)

    def _get_ttl(self, expiry):
        if expiry is not None and expiry > 0:
            return expiry - int(time.time() * 1000)
        return None
    
    def _get_expiry(self, ttl):
        if ttl is not None and ttl > 0:
            return int(time.time() * 1000) + (ttl * 1000)
        return -1

    def _get_from_postgres(self, key):
        """Get a document by key. Returns value or raises KeyError."""
        with self._connection.cursor() as cursor:
            try:
                cursor.execute("SELECT value, compressed, ttl FROM %s WHERE id = %%s" % self.postgres_table_name, (key,))
                results = cursor.fetchall()
            except Exception as e:
                traceback.print_exc()
                raise e
            finally:
                cursor.close()
            if len(results) == 0:
                raise KeyError()
            result_row = results[0]
            result_ttl = self._get_ttl(result_row[2])
            if result_ttl is not None and result_ttl <= 0:
                raise KeyError()
            value = self._convert_to_value(result_row[0], result_row[2])
            return value

    def _set_in_postgres(self, key, value, ttl=None):
        """Set (upsert) a document."""
        new_cas = time.time_ns()
        compressed, value_bytes = self._get_value_bytes(value)
        expiry = self._get_expiry(ttl)
        with self._connection.cursor() as cursor:
            try:
                query_string = (
                    "INSERT INTO %s (id, value, cas, compressed, expiry) " \
                    "VALUES (%%s, %%s, %%s, %%s, %%s) ON CONFLICT (id) " \
                    "DO UPDATE SET value = EXCLUDED.value, cas = EXCLUDED.cas, compressed = EXCLUDED.compressed, expiry = EXCLUDED.expiry"
                )
                cursor.execute(
                    query_string % self.postgres_table_name,
                    (key, value_bytes, new_cas, compressed, expiry)
                )
            except:
                traceback.print_exc()
            finally:
                cursor.close()

    def _remove_from_postgres(self, key, cas=None):
        """Remove a document."""
        with self._connection.cursor() as cursor:
            try:
                cursor.execute(
                    "DELETE FROM %s WHERE id = %%s" % self.postgres_table_name,
                    (key,)
                )
            except:
                traceback.print_exc()
            finally:
                cursor.close()

    def __contains__(self, item):
        try:
            self._get_from_postgres(self._get_entry_key(item))
            return True
        except KeyError:
            return False

    def __getitem__(self, item):
        return self._get_from_postgres(self._get_entry_key(item))

    def __setitem__(self, key, value):
        self._set_in_postgres(self._get_entry_key(key), value)

    def __delitem__(self, item):
        self._remove_from_postgres(self._get_entry_key(item))

    def pop(self, item):
        value = self._get_from_postgres(self._get_entry_key(item))
        self._remove_from_postgres(self._get_entry_key(item))
        return value

    def _get_keys(self, include_docs=False):
        """Get items by table name."""
        query = "SELECT id FROM %s WHERE id like '%s:%%'" % (self.postgres_table_name, self.table_name)
        if include_docs:
            query = "SELECT id, value, compressed FROM %s WHERE id like '%s:%%'" % (self.postgres_table_name, self.table_name)
        with self._connection.cursor() as cursor:
            try:
                cursor.execute(query)
                table_rows = cursor.fetchall()
            finally:
                cursor.close()
        
        table_values = []
        for row in table_rows:
            doc_id = row[0]
            value_obj = {"key": doc_id.replace(self.table_name + ":", "")}

            if include_docs:
                value_obj["document"] = self._convert_to_value(row[1], row[2])
                continue

            table_values.append(value_obj)
        return table_values

    def __iter__(self):
        values = self._get_keys()
        for item in values:
            yield item["key"]

    def __len__(self):
        values = self._get_keys()
        return len(values)

    def items(self):
        values = self._get_keys(include_docs=True)
        yield [(item["key"], item["document"]) for item in values]

    def iteritems(self, *args, **kwargs):
        values = self._get_keys(include_docs=True)
        for item in values:
            yield item["key"], item["document"]

    def keys(self):
        values = self._get_keys()
        yield [item["key"] for item in values]

    def iterkeys(self):
        values = self._get_keys()
        for item in values:
            yield item["key"]

    def values(self):
        values = self._get_keys(include_docs=True)
        yield [item["document"] for item in values]

    def itervalues(self):
        values = self._get_keys(include_docs=True)
        for item in values:
            yield item["document"]

class PostgresBackend(object):

    def __init__(self, db_host='localhost', db_user='postgres', db_password='', db_name='default', db_table_name='kvstore.kv_store', users_table_name='User',
            roles_table_name='Role', pending_reg_table_name='Register'):
        """Data storage class. Handles JSON Docs in Couchbase

        :param db_host: hostname of postgres server to use
        :type db_host: str.
        :param db_user: username used to log into postgres server
        :type db_user: str.
        :param db_password: password used to log into postgres server
        :type db_password: str.
        :param db_name: name of the database to use
        :type db_name: str.
        :param db_table_name: name of the table to use
        :type db_table_name: str.
        :param users_table_name: prefix for user keys
        :type users_table_name: str.
        :param roles_table_name: prefix for role keys
        :type roles_table_name: str.
        :param pending_reg_table_name: prefix for pending registration keys
        :type pending_reg_table_name: str.
        """
        import psycopg2
        self.connection = psycopg2.connect(host=db_host, dbname=db_name, user=db_user, password=db_password, autocommit=True)
        self.users = PostgresTable(self.connection, db_table_name, users_table_name)
        self.roles = PostgresTable(self.connection, db_table_name, roles_table_name)
        self.pending_registrations = PostgresTable(self.connection, db_table_name, pending_reg_table_name)

class CouchbaseTable(dict):
    def __init__(self, bucket, table_name):
        """ Wrapper class to manage a table of couchbase entries

        :param bucket: couchbase Bucket
        :type bucket: couchbase.bucket.Bucket
        :param table_name: the name (aka prefix) of the table entries
        :type table_name: str.
        """
        self.bucket = bucket
        self.client = bucket.default_collection()
        self.table_name = table_name

    def _get_entry_key(self, item):
        return "%s:%s" % (self.table_name, item)

    def __contains__(self, item):
        try:
            result = self.client.get(self._get_entry_key(item))
        except:
            return False
        return result.content_as[dict] is not None

    def __getitem__(self, item):
        try:
            result = self.client.get(self._get_entry_key(item))
        except:
            raise KeyError()

        return result.content_as[dict]

    def __setitem__(self, key, value):
        try:
            self.client.upsert(self._get_entry_key(key), value)
        except:
            pass

    def __delitem__(self, item):
        try:
            self.client.remove(self._get_entry_key(item))
        except:
            pass

    def pop(self, item):
        try:
            result = self.client.get(self._get_entry_key(item))
            self.client.remove(self._get_entry_key(item))
        except:
            raise KeyError()

        return result.content_as[dict]

    def _get_keys(self, include_docs=False):
        from couchbase.options import ViewOptions
        view_values = [v for v in self.bucket.view_query(COUCHBASE_ENTRY_DESIGN_DOC, COUCHBASE_ENTRY_VIEW, ViewOptions(key=self.table_name, reduce=False)).rows()]
        # seems that couchbase sdk removed include_docs
        if include_docs:
            doc_ids = [r.id for r in view_values]
            multi_response = self.client.get_multi(doc_ids)
            multi_results = multi_response.results
            for value in view_values:
                value.document = multi_results[value.id]
        return view_values

    def __iter__(self):
        values = self._get_keys()
        for item in values:
            yield item.key

    def __len__(self):
        values = self._get_keys()
        return len(values)

    def items(self):
        values = self._get_keys(include_docs=True)
        yield [(item.key, item.document.content_as[dict]) for item in values]

    def iteritems(self, *args, **kwargs):
        values = self._get_keys(include_docs=True)
        for item in values:
            yield item.key, item.document.content_as[dict]

    def keys(self):
        values = self._get_keys()
        yield [item.key for item in values]

    def iterkeys(self):
        values = self._get_keys()
        for item in values:
            yield item.key

    def values(self):
        values = self._get_keys(include_docs=True)
        yield [item.document.content_as[dict] for item in values]

    def itervalues(self):
        values = self._get_keys(include_docs=True)
        for item in values:
            yield item.document.content_as[dict]

class CouchbaseBackend(object):

    def __init__(self, db_host='localhost', db_password='', db_bucket='default', users_table_name='User',
            roles_table_name='Role', pending_reg_table_name='Register'):
        """Data storage class. Handles JSON Docs in Couchbase

        :param db_host: hostname of couchbase server to use
        :type db_host: str.
        :param db_password: password used to log into couchbase server
        :type db_password: str.
        :param db_bucket: couchbase bucket that contains the data
        :type db_bucket: str.
        :param users_table_name: prefix for user keys
        :type users_table_name: str.
        :param roles_table_name: prefix for role keys
        :type roles_table_name: str.
        :param pending_reg_table_name: prefix for pending registration keys
        :type pending_reg_table_name: str.
        """
        from couchbase.cluster import Cluster
        from couchbase.options import ClusterOptions
        from couchbase.auth import PasswordAuthenticator
        cluster = Cluster('couchbase://{0}'.format(db_host), ClusterOptions(PasswordAuthenticator(db_bucket, db_password)))
        bucket = cluster.bucket(db_bucket)
        self.users = CouchbaseTable(bucket, users_table_name)
        self.roles = CouchbaseTable(bucket, roles_table_name)
        self.pending_registrations = CouchbaseTable(bucket, pending_reg_table_name)


class Cork(object):

    def __init__(self, email_sender=None, db_host='localhost', db_password='', db_bucket='default',
        users_table_name='User', roles_table_name='Role', pending_reg_table_name='Register', 
        postgres_config=None, session_domain=None, smtp_url='localhost', smtp_server=None):
        """Auth/Authorization/Accounting class

        :param db_host: hostname of couchbase server to use
        :type db_host: str.
        :param db_password: password used to log into couchbase server
        :type db_password: str.
        :param db_bucket: couchbase bucket that contains the data
        :type db_bucket: str.
        :param users_table_name: prefix for user keys
        :type users_table_name: str.
        :param roles_table_name: prefix for role keys
        :type roles_table_name: str.
        :param pending_reg_table_name: prefix for pending registration keys
        :type pending_reg_table_name: str.
        :param postgres_config: configuration for postgres server
        :type postgres_config: dict.
        :param session_domain: domain for the session cookie
        :type session_domain: str.
        :param smtp_url: URL for the SMTP server
        :type smtp_url: str.
        :param smtp_server: SMTP server to use
        :type smtp_server: str.
        """
        if smtp_server:
            smtp_url = smtp_server
        self.mailer = Mailer(email_sender, smtp_url)
        if postgres_config is not None:
            self._store = PostgresBackend(postgres_config['host'], postgres_config['user'], 
                postgres_config['password'], postgres_config['dbname'], postgres_config['table_name'],
                users_table_name, roles_table_name, pending_reg_table_name)
        else:
            self._store = CouchbaseBackend(db_host, db_password, db_bucket, users_table_name,
                                       roles_table_name, pending_reg_table_name)
        self.password_reset_timeout = 3600 * 24
        self.session_domain = session_domain

    def login(self, username, password, success_redirect=None,
        fail_redirect=None):
        """Check login credentials for an existing user.
        Optionally redirect the user to another page (tipically /login)

        :param username: username
        :type username: str.
        :param password: cleartext password
        :type password: str.
        :param success_redirect: redirect authorized users (optional)
        :type success_redirect: str.
        :param fail_redirect: redirect unauthorized users (optional)
        :type fail_redirect: str.
        :returns: True for successful logins, else False
        """
        assert isinstance(username, str), "the username must be a string"
        assert isinstance(password, str), "the password must be a string"

        if username in self._store.users:
            if self._verify_password(username, password,
                    self._store.users[username]['hash']):
                # Setup session data
                self._setup_cookie(username)
                if success_redirect:
                    bottle.redirect(success_redirect)
                return True

        if fail_redirect:
            bottle.redirect(fail_redirect)

        return False

    def logout(self, success_redirect='/login', fail_redirect='/login'):
        """Log the user out, remove cookie

        :param success_redirect: redirect the user after logging out
        :type success_redirect: str.
        :param fail_redirect: redirect the user if it is not logged in
        :type fail_redirect: str.
        """
        try:
            session = bottle.request.environ.get('beaker.session')
            session.delete()
            bottle.redirect(success_redirect)
        except:
            bottle.redirect(fail_redirect)

    def require(self, username=None, company=None, role=None, fixed_role=False,
        fail_redirect=None):
        """Ensure the user is logged in has the required role (or higher).
        Optionally redirect the user to another page (tipically /login)
        If both `username` and `role` are specified, both conditions need to be
        satisfied.
        If none is specified, any authenticated user will be authorized.
        By default, any role with higher level than `role` will be authorized;
        set fixed_role=True to prevent this.

        :param username: username (optional)
        :type username: str.
        :param role: role
        :type role: str.
        :param fixed_role: require user role to match `role` strictly
        :type fixed_role: bool.
        :param redirect: redirect unauthorized users (optional)
        :type redirect: str.
        """
        # Parameter validation
        if username is not None:
            if username not in self._store.users:
                raise AAAException("Nonexistent user")

        if fixed_role and role is None:
            raise AAAException(
                """A role must be specified if fixed_role has been set""")

        if role is not None and role not in self._store.roles:
            raise AAAException("Role not found")

        # Authentication
        try:
            cu = self.current_user
        except AAAException:
            if fail_redirect is None:
                raise AuthException("Unauthenticated user")
            else:
                bottle.redirect(fail_redirect)

        if cu.role not in self._store.roles:
            raise AAAException("Role not found for the current user")

        if username is not None:
            if username != self.current_user.username:
                if fail_redirect is None:
                    raise AuthException("""Unauthorized access: incorrect
                        username""")
                else:
                    bottle.redirect(fail_redirect)

        if company is not None and cu.level < 200:
            if cu.info["company"] != company:
                if fail_redirect is None:
                    raise AuthException("""Unauthorized access: user is not
                        associated with company""")
                else:
                    bottle.redirect(fail_redirect)

        if fixed_role:
            if role == self.current_user.role:
                return

            if fail_redirect is None:
                raise AuthException("Unauthorized access: incorrect role")
            else:
                bottle.redirect(fail_redirect)

        else:
            if role is not None:
                # Any role with higher level is allowed
                current_lvl = self._store.roles[self.current_user.role]["level"]
                threshold_lvl = self._store.roles[role]["level"]
                if current_lvl >= threshold_lvl:
                    return

                if fail_redirect is None:
                    raise AuthException("Unauthorized access: ")
                else:
                    bottle.redirect(fail_redirect)

        return

    def create_role(self, role, level):
        """Create a new role.

        :param role: role name
        :type role: str.
        :param level: role level (0=lowest, 100=admin)
        :type level: int.
        :raises: AuthException on errors
        """
        if self.current_user.level < 100:
            raise AuthException("The current user is not authorized to ")
        if role in self._store.roles:
            raise AAAException("The role is already existing")
        try:
            int(level)
        except ValueError:
            raise AAAException("The level must be numeric.")
        self._store.roles[role] = {"level": level}

    def delete_role(self, role):
        """Deleta a role.

        :param role: role name
        :type role: str.
        :raises: AuthException on errors
        """
        if self.current_user.level < 100:
            raise AuthException("The current user is not authorized to ")
        if role not in self._store.roles:
            raise AAAException("Nonexistent role.")
        self._store.roles.pop(role)

    def list_roles(self):
        """List roles.

        :returns: (role, role_level) generator (sorted by role)
        """
        for role in sorted(self._store.roles):
            yield (role, self._store.roles[role]["level"])

    def create_user(self, username, role, password, company, email_addr=None,
        permissions={}):
        """Create a new user account.
        This method is available to users with level>=100

        :param username: username
        :type username: str.
        :param role: role
        :type role: str.
        :param password: cleartext password
        :type password: str.
        :param email_addr: email address (optional)
        :type email_addr: str.
        :param permissions: this is the list of granted permissions of the user
        :type permissions: dict
        :raises: AuthException on errors
        """
        assert username, "Username must be provided."
        assert company, "Company must be provided."
        assert isinstance(permissions, dict), "Permissions must be a dictionary"
        if self.current_user.level < 100:
            raise AuthException("The current user is not authorized to ")
        if username in self._store.users:
            raise AAAException("User is already existing.")
        if role not in self._store.roles:
            raise AAAException("Nonexistent user role.")
        tstamp = int(time())
        self._store.users[username] = {
            'role': role,
            'hash': self._hash(username, password),
            'email_addr': email_addr,
            'company': company,
            'perm': permissions,
            'validated': True,
            'creation_date': tstamp
        }

    def delete_user(self, username):
        """Delete a user account.
        This method is available to users with level>=100

        :param username: username
        :type username: str.
        :raises: Exceptions on errors
        """
        if self.current_user.level < 100:
            raise AuthException("The current user is not authorized to ")
        if username not in self._store.users:
            raise AAAException("Nonexistent user.")
        self.user(username).delete()

    def list_users(self):
        """List users.

        :return: (username, role, email_addr, description) generator (sorted by
        username)
        """
        for un in sorted(self._store.users):
            d = self._store.users[un]
            yield (un, d['validated'], d['role'], d['email_addr'], d['company'], d['perm'])

    @property
    def current_user(self):
        """Current autenticated user

        :returns: User() instance, if authenticated
        :raises: AuthException otherwise
        """
        session = self._beaker_session
        username = session.get('username', None)
        if username is None:
            raise AuthException("Unauthenticated user")
        if username is not None and username in self._store.users:
            return User(username, self, session=session)
        raise AuthException("Unknown user: %s" % username)

    def user(self, username):
        """Existing user

        :returns: User() instance if the user exist, None otherwise
        """
        if username is not None and username in self._store.users:
            return User(username, self)
        return None

    def register(self, username, password, email_addr, company, role='user',
        max_level=50, subject="Signup confirmation",
        email_template=None, permissions={}):
        """Register a new user account. An email with a registration validation
        is sent to the user.
        WARNING: this method is available to unauthenticated users

        :param username: username
        :type username: str.
        :param password: cleartext password
        :type password: str.
        :param role: role (optional), defaults to 'user'
        :type role: str.
        :param max_level: maximum role level (optional), defaults to 50
        :type max_level: int.
        :param email_addr: email address
        :type email_addr: str.
        :param subject: email subject
        :type subject: str.
        :param email_template: email template filename
        :type email_template: str.
        :param permissions: dictionary of granted permissions
        :type permissions: dict
        :raises: AssertError or AAAException on errors
        """
        assert username, "Username must be provided."
        assert password, "A password must be provided."
        assert email_addr, "An email address must be provided."
        assert company, "An company must be provided."
        assert isinstance(permissions, dict), "Permissions must be a dictionary"
        if username in self._store.users:
            raise AAAException("User is already existing.")
        if role not in self._store.roles:
            raise AAAException("Nonexistent role")
        if self._store.roles[role]["level"] > max_level:
            raise AAAException("Unauthorized role")

        registration_code = uuid.uuid4().hex
        creation_date = int(time())

        if email_template:
            # send registration email
            email_text = bottle.template(email_template,
                username=username,
                email_addr=email_addr,
                company=company,
                role=role,
                creation_date=creation_date,
                registration_code=registration_code
            )
            self.mailer.send_email(email_addr, subject, email_text)

        # store pending registration
        self._store.pending_registrations[registration_code] = {
            'username': username,
            'role': role,
            'hash': self._hash(username, password),
            'email_addr': email_addr,
            'company': company,
            'perm': permissions,
            'creation_date': creation_date,
        }

        return registration_code

    def validate_registration(self, registration_code):
        """Validate pending account registration, create a new account if
        successful.

        :param registration_code: registration code
        :type registration_code: str.
        """
        try:
            data = self._store.pending_registrations.pop(registration_code)
        except KeyError:
            raise AuthException("Invalid registration code.")

        username = data['username']
        if username in self._store.users:
            raise AAAException("User is already existing.")

        # the user data is moved from pending_registrations to _users
        self._store.users[username] = {
            'role': data['role'],
            'hash': data['hash'],
            'email_addr': data['email_addr'],
            'company': data['company'],
            'perm': data['perm'],
            'validated': False,
            'creation_date': data['creation_date']
        }
        return username

    def send_password_reset_email(self, username=None, email_addr=None,
        subject="Password reset confirmation",
        email_template='views/password_reset_email'):
        """Email the user with a link to reset his/her password
        If only one parameter is passed, fetch the other from the users
        database. If both are passed they will be matched against the users
        database as a security check

        :param username: username
        :type username: str.
        :param email_addr: email address
        :type email_addr: str.
        :param subject: email subject
        :type subject: str.
        :param email_template: email template filename
        :type email_template: str.
        :raises: AAAException on missing username or email_addr,
            AuthException on incorrect username/email_addr pair
        """
        if username is None:
            if email_addr is None:
                raise AAAException("At least `username` or `email_addr` must" \
                    " be specified.")

            # only email_addr is specified: fetch the username
            for k, v in self._store.users.iteritems():
                if v['email_addr'] == email_addr:
                    username = k
                    break
                raise AAAException("Email address not found.")

        else:  # username is provided
            if username not in self._store.users:
                raise AAAException("Nonexistent user.")
            if email_addr is None:
                email_addr = self._store.users[username].get('email_addr', None)
                if not email_addr:
                    raise AAAException("Email address not available.")
            else:
                # both username and email_addr are provided: check them
                stored_email_addr = self._store.users[username]['email_addr']
                if email_addr != stored_email_addr:
                    raise AuthException("Username/email address pair not found.")

        # generate a reset_code token
        reset_code = self._reset_code(username, email_addr)

        # send reset email
        email_text = bottle.template(email_template,
            username=username,
            email_addr=email_addr,
            reset_code=reset_code
        )
        self.mailer.send_email(email_addr, subject, email_text)

    def reset_password(self, reset_code, password):
        """Validate reset_code and update the account password
        The username is extracted from the reset_code token

        :param reset_code: reset token
        :type reset_code: str.
        :param password: new password
        :type password: str.
        :raises: AuthException for invalid reset tokens, AAAException
        """
        try:
            reset_code = b64decode(reset_code)
            username, email_addr, tstamp, h = reset_code.split(':', 3)
            tstamp = int(tstamp)
        except (TypeError, ValueError):
            raise AuthException("Invalid reset code.")
        if time() - tstamp > self.password_reset_timeout:
            raise AuthException("Expired reset code.")
        if not self._verify_password(username, email_addr, h):
            raise AuthException("Invalid reset code.")
        user = self.user(username)
        if user is None:
            raise AAAException("Nonexistent user.")
        user.update(pwd=password)

    def verify_password(self, username, password):
        return self._verify_password(username, password,
                    self._store.users[username]['hash'])

    # # Private methods

    @property
    def _beaker_session(self):
        """Get Beaker session"""
        return bottle.request.environ.get('beaker.session')

    def _setup_cookie(self, username):
        """Setup cookie for a user that just logged in"""
        session = bottle.request.environ.get('beaker.session')
        session['username'] = username
        if self.session_domain is not None:
            session.domain = self.session_domain
        session.save()

    @staticmethod
    def _hash(username, pwd, salt=None):
        """Hash username and password, generating salt value if required
        Use PBKDF2 from Beaker

        :returns: base-64 encoded str.
        """
        if salt is None:
            salt = os.urandom(32)
        assert len(salt) == 32, "Incorrect salt length"

        cleartext = "%s\0%s" % (username, pwd)
        h = crypto.generateCryptoKeys(cleartext, salt, 10, 32)
        if len(h) != 32:
            raise RuntimeError("The PBKDF2 hash is not 32bytes long")

        # 'p' for PBKDF2
        return b64encode(b'p' + salt + h).decode("utf-8")

    @classmethod
    def _verify_password(cls, username, pwd, salted_hash):
        """Verity username/password pair against a salted hash

        :returns: bool
        """
        decoded = b64decode(salted_hash)
        hash_type = chr(decoded[0])
        if hash_type != 'p':  # 'p' for PBKDF2
            return False  # Only PBKDF2 is supported

        salt = decoded[1:33]
        return cls._hash(username, pwd, salt) == salted_hash

    def _purge_expired_registrations(self, exp_time=96):
        """Purge expired registration requests.

        :param exp_time: expiration time (hours)
        :type exp_time: float.
        """
        for uuid, data in self._store.pending_registrations.items():
            creation = data['creation_date']
            now = int(time())
            maxdelta = (exp_time * 60 * 60)
            if now - creation > maxdelta:
                self._store.pending_registrations.pop(uuid)

    def _reset_code(self, username, email_addr):
        """generate a reset_code token

        :param username: username
        :type username: str.
        :param email_addr: email address
        :type email_addr: str.
        :returns: Base-64 encoded token
        """
        h = self._hash(username, email_addr)
        t = "%d" % time()
        reset_code = ':'.join((username, email_addr, t, h))
        return b64encode(reset_code)

class User(object):

    def __init__(self, username, cork_obj, session=None):
        """Represent an authenticated user, exposing useful attributes:
        username, role, level, session_creation_time, session_accessed_time,
        session_id. The session-related attributes are available for the
        current user only.

        :param username: username
        :type username: str.
        :param cork_obj: instance of :class:`Cork`
        """
        self._cork = cork_obj
        assert username in self._cork._store.users, "Unknown user"
        self.username = username
        self.info = self._cork._store.users[username]
        self.__load_attributes()

        if session is not None:
            try:
                self.session_creation_time = session['_creation_time']
                self.session_accessed_time = session['_accessed_time']
                self.session_id = session['_id']
            except:
                pass

    def __load_attributes(self):
        self.company = self.info['company']
        self.permissions = self.info['perm']
        self.email_addr = self.info['email_addr']
        self.permissions = self.info["perm"]
        self.role = self.info['role']
        self.level = self._cork._store.roles[self.role]["level"]

    def update(self, role=None, pwd=None, email_addr=None, validated=None, permissions=None, company=None):
        """Update an user account data

        :param role: change user role, if specified
        :type role: str.
        :param pwd: change user password, if specified
        :type pwd: str.
        :param email_addr: change user email address, if specified
        :type email_addr: str.
        :param permissions: add to user permissions, if specified
        :type permissions: dict
        :raises: AAAException on nonexistent user or role.
        """
        username = self.username
        if username not in self._cork._store.users:
            raise AAAException("User does not exist.")

        user_obj = self._cork._store.users[username]

        if role is not None:
            if role not in self._cork._store.roles:
                raise AAAException("Nonexistent role.")
            user_obj['role'] = role
        if pwd is not None:
            user_obj['hash'] = self._cork._hash(username, pwd)
        if email_addr is not None:
            user_obj['email_addr'] = email_addr
        if permissions is not None:
            assert isinstance(permissions, dict), "Permissions must be a dictionary"
            user_obj['perm'].update(permissions)
        if validated is not None:
            user_obj['validated'] = True
        if company is not None:
            user_obj['company'] = company

        self.info = user_obj
        self.__load_attributes()
        self._cork._store.users[username] = user_obj

    def remove_permissions(self, permissions):
        """Remove permissions from a user account data

        :param permissions: removed permissions from user
        :type permissions: list
        :raises: AAAException on nonexistent user or role.
        """
        assert isinstance(permissions, list), "Permissions must be list"

        username = self.username
        if username not in self._cork._store.users:
            raise AAAException("User does not exist.")

        user_obj = self._cork._store.users[username]

        for perm in permissions:
            try:
                del user_obj["perm"][perm]
            except:
                pass

        self.info = user_obj
        self.__load_attributes()
        self._cork._store.users[username] = user_obj

    def delete(self):
        """Delete user account

        :raises: AAAException on nonexistent user.
        """
        try:
            self._cork._store.users.pop(self.username)
        except KeyError:
            raise AAAException("Nonexistent user.")

class Mailer(object):

    def __init__(self, sender, smtp_url, join_timeout=5):
        """Send emails asyncronously

        :param sender: Sender email address
        :type sender: str.
        :param smtp_server: SMTP server
        :type smtp_server: str.
        """
        self.sender = sender
        self.join_timeout = join_timeout
        self._threads = []
        self._conf = self._parse_smtp_url(smtp_url)

    def _parse_smtp_url(self, url):
        """Parse SMTP URL"""
        match = re.match(r"""
            (                                   # Optional protocol
                (?P<proto>smtp|starttls|ssl)    # Protocol name
                ://
            )?
            (                                   # Optional user:pass@
                (?P<user>[^:]*)                 # Match every char except ':'
                (: (?P<pass>.*) )? @           # Optional :pass
            )?
            (?P<fqdn>.*?)                       # Required FQDN
            (                                   # Optional :port
                :
                (?P<port>[0-9]{,5})             # Up to 5-digits port
            )?
            [/]?
            $
        """, url, re.VERBOSE)

        if not match:
            raise RuntimeError("SMTP URL seems incorrect")

        d = match.groupdict()
        if d['proto'] is None:
            d['proto'] = 'smtp'

        if d['port'] is None:
            d['port'] = 25
        else:
            d['port'] = int(d['port'])

        return d



    def send_email(self, email_addr, subject, email_text):
        """Send an email

        :param email_addr: email address
        :type email_addr: str.
        :param subject: subject
        :type subject: str.
        :param email_text: email text
        :type email_text: str.
        :raises: AAAException if smtp_server and/or sender are not set
        """
        if not (self._conf['fqdn'] and self.sender):
            raise AAAException("SMTP server or sender not set")
        msg = MIMEMultipart('alternative')
        msg['Subject'] = subject
        msg['From'] = self.sender
        msg['To'] = email_addr
        part = MIMEText(email_text, 'html')
        msg.attach(part)

        log.debug("Sending email using %s" % self._conf['fqdn'])
        thread = Thread(target=self._send, args=(email_addr, msg.as_string()))
        thread.start()
        self._threads.append(thread)

    def _send(self, email_addr, msg):  # pragma: no cover
        """Deliver an email using SMTP

        :param email_addr: recipient
        :type email_addr: str.
        :param msg: email text
        :type msg: str.
        """
        proto = self._conf['proto']
        assert proto in ('smtp', 'starttls', 'ssl'), \
            "Incorrect protocol: %s" % proto

        try:
            if proto == 'ssl':
                log.debug("Setting up SSL")
                session = SMTP_SSL(self._conf['fqdn'])
            else:
                session = SMTP(self._conf['fqdn'])

            if proto == 'starttls':
                log.debug('Sending EHLO and STARTTLS')
                session.ehlo()
                session.starttls()
                session.ehlo()

            if self._conf['user'] is not None:
                log.debug('Performing login')
                session.login(self._conf['user'], self._conf['pass'])

            log.debug('Sending')
            session.sendmail(self.sender, email_addr, msg)
            session.quit()
            log.info('Email sent')

        except Exception as e:
            log.error("Error sending email: %s" % e, exc_info=True)

    def join(self):
        """Flush email queue by waiting the completion of the existing threads

        :returns: None
        """
        return [t.join(self.join_timeout) for t in self._threads]

    def __del__(self):
        """Class destructor: wait for threads to terminate within a timeout"""
        self.join()

