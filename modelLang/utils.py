from collections import defaultdict

class customdefdict(defaultdict):
    def __missing__(self, key):
        if self.default_factory is None:
            raise KeyError(key)
        item = self.default_factory(key)
        self[key] = item
        return item
