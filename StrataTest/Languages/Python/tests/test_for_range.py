numbers = [2,4,5,9,1]

for i in range(5):
    assert i < 5
    assert i >= 0
    j = numbers [i]
    assert j < 10


for i in range(-10):
    assert i >= -10
    assert i < 0
    j = numbers[i+5]
    assert j < 10
