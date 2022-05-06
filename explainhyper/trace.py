
class Trace:
    prefix = []
    lasso = []

    def get_length(self):
        return len(self.prefix) + len(self.lasso)

    def value_at(self, x):
        full_trace = self.prefix + self.lasso
        if len(full_trace)-1 < x:
            return 0
        return full_trace[x]

    def is_liveness(self):
        return len(self.lasso) > 0

    def set_values(self, param):
        self.prefix = param

    def set_lasso(self, lasso):
        self.lasso = lasso

    def __str__(self) -> str:
        return str(self.prefix + self.lasso)
