xs = [1, 2]
xs.some_unmodeled_call(3)
assert xs == [1, 2], "expected unknown because xs should be havocked"
