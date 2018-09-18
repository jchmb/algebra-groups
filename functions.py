import itertools

def powerset(A):
	yield tuple([])
	for i in range(1, len(A)):
		for combination in itertools.combinations(A, i):
			yield combination
	yield tuple(A)