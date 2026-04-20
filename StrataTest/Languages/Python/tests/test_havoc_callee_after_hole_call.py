xs = [1, 2]
xs.some_unmodeled_call_1(3)
assert xs == [1, 2], "expected unknown because xs should be havocked"


xs = [1,2]
ys = xs.some_unmodeled_call_2()
assert xs == [1, 2], "expected unknown because xs should be havocked" 


