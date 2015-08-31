""" Base classes for computing fingerprints and exportable versions
    of objects.
"""

import json
from gmpy import mpz
# from gmpy2 import mpz, bit_length, f_divmod_2exp
from base64 import b64encode
from hashlib import sha256 as crypthash

import utils

def fingerprint(blob):
    """Compute the fingerprint of its input.
       This blob can contain an integer, a string, a dict or
       an object with a fingerprint method.
    """
    # is it an integer?
    try:
        mpz_value = mpz(blob)
    except (TypeError, ValueError):
        pass
    else:
        string = utils.mpztob64(mpz_value)
        return b64encode(crypthash(string).digest())

    # is it a string?
    if isinstance(blob, str):
        return b64encode(crypthash(blob).digest())
    # is it a list?
    if isinstance(blob, (list, tuple)):
        list_of_fingerprints = [fingerprint(i) for i in blob]
        string = json.dumps(list_of_fingerprints, separators=(',',':'))
        return b64encode(crypthash(string).digest())
    # is it a dict?
    if isinstance(blob, dict):
        # is this dict already a hash of something?
        if "#" in blob:
            return blob["#"]
        # otherwise, transform dict into array and fingerprint it
        keys = sorted(blob)
        list_of_fingerprints = [fingerprint([k, blob[k]]) \
                                    for k in keys]
        string = json.dumps(list_of_fingerprints, separators=(',',':'))
        return b64encode(crypthash(string).digest())
    # is it None
    if blob is None:
        return fingerprint('None')
    # is it an object?
    try:
        # is it a class for which we can compute a fingerprint?
        return blob.fingerprint()
    except AttributeError:
        pass
    assert False, "fingerprint cannot parse object"

def exportable(blob, f_dict = None):
    """Produces something that only contains strings, lists and dicts,
    so that it can be given as input for json.dumps for instance.
    In particular:
    - convert all integers to base64
    - make sure that all elements of all lists can be dumped
    - make sure that all elements of all dictionaries can be dumped
    - convert other objects into a dictionary that can be dumped
    """
    if f_dict is None:
        f_dict = {}
    # is it an integer?
    try:
        mpz_value = mpz(blob)
    except (TypeError, ValueError):
        pass
    else:
        return utils.mpztob64(mpz_value), f_dict
    # is it a class for which we can compute a fingerprint?
    try:
        result, f_dict = blob.exportable(f_dict)
        return result, f_dict
    except AttributeError:
        pass
    # is it a string?
    if isinstance(blob, str):
        return blob, f_dict
    # is it a list?
    elif isinstance(blob, (list, tuple)):
        result = []
        for b in blob:
            e, f_dict = exportable(b, f_dict)
            result.append(e)
        return result, f_dict
    # is it a dictionary?
    elif isinstance(blob, dict):
        dict_to_export = {}
        for k in blob.keys():
            dict_to_export[k], f_dict = exportable(blob[k], f_dict)
        return dict_to_export, f_dict
    print "I cannot parse this:", blob
    assert False, "exportable cannot parse object"

class FingExp(object):
    """ Base class for exporting and computing the fingerprint of
        objects.
    """

    def __init__(self):
        self.type = self.__class__.__module__.split(".")[-1] + \
            "/" + self.__class__.__name__
        self.to_fingerprint.append("type")
        self.to_export["value"].append("type")

    def __setattr__(self, name, value):
        object.__setattr__(self, name, value)
        try:
            self.attr_fingerprint[name] = None
        except:
            self.attr_fingerprint = {name: None}
        self.attr_fingerprint["#"] = None
        # print "change!", self.attr_fingerprint

    def fingerprint(self):
        """Compute the fingerprint of the object, as a base64 string.
        It tries to not recompute the same hash many times by implementing
        some tracking. However, this tracking only works for attributes.
        As a result, it will for instance not detect changes in lists or dicts.
        """
        # check whether the hash of this object is already known
        if self.attr_fingerprint["#"] is not None:
            return self.attr_fingerprint["#"]
        list_to_hash = []
        # Going through all fields that need to be taken into account
        for key in sorted(self.to_fingerprint):
            # Computing missing hashes
            if self.attr_fingerprint[key] is None:
                self.attr_fingerprint[key] = \
		    fingerprint([key, getattr(self, key)])
            # Building final string
            list_to_hash.append(self.attr_fingerprint[key])
        string = json.dumps(list_to_hash, separators=(',',':'))
        result = b64encode(crypthash(string).digest())
        self.attr_fingerprint["#"] = result
        return result

    def exportable(self, f_dict = None):
        """Export the object as a dictionary that can then be exported
	   easily (e.g., jsonified).
	"""
        if f_dict is None:
            f_dict = {}
        dict_to_export = {}
        # Going through all fields that need to be taken into account
        for key in sorted(self.to_export["fingerprint"]):
            f_attr = fingerprint(getattr(self, key))
            dict_to_export[key] = {"#": f_attr}
            if not f_attr in f_dict:
                f_dict[f_attr], f_dict = exportable(getattr(self, key), f_dict)
        for key in sorted(self.to_export["value"]):
            dict_to_export[key], f_dict = exportable(getattr(self, key), f_dict)
        return dict_to_export, f_dict








