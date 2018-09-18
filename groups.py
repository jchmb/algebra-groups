from functions import *
from itertools import *
import math

'''
Group class. Encapsulates a group with a given operation fn: G x G -> G.
'''
class Group:
	'''
	Constructor.

	:param group elements
	:param group operator
	'''
	def __init__(self, elements, fn):
		self.elements = elements
		self.fn = fn
		self.cache_identity()
		self.cache_inverses()

	@staticmethod
	def from_file(filename):
		with open(filename) as f:
			elements = []
			rows = {}
			for row in f:
				row_elements = row.split()
				a = row_elements.pop(0)
				elements.append(a)
				rows[a] = row_elements
			mappings = {}
			for a, row in rows.items():
				for i in range(len(row)):
					c = row[i]
					b = elements[i]
					mappings[(a, b)] = c
			return Group(elements, lambda x, y: mappings[(x, y)])
		return None

	def cache_identity(self):
		for a in self.elements:
			if self.is_identity(a):
				self.identity = a
				break

	'''
	Check if a is the identity, i.e., f(a, g) = g for all g in G.
	'''
	def is_identity(self, a):
		for b in self.elements:
			if self.fn(a, b) != b or self.fn(b, a) != b:
				return False
		return True

	def cache_inverses(self):
		self.inverses = {}
		for g in self.elements:
			self.inverses[g] = self.inverse(g)

	'''
	Apply the group operation.
	'''
	def operation(self, a, b):
		return self.fn(a, b)

	'''
	Apply a n times to itself.
	'''
	def powerOf(self, a, n):
		b = a
		if n == 0:
			return self.identity
		for i in range(abs(n)):
			c = a if n > 0 else self.inverse(a)
			b = self.operation(b, c)
		return b

	'''
	Compute the inverse of a, i.e., find the g in G such that f(a, g) = e.
	'''
	def inverse(self, a):
		for b in self.elements:
			if self.operation(a, b) == self.identity:
				return b
		return None

	'''
	Compute the left coset for the given subgroup of G and the given element a.
	'''
	def left_coset(self, subgroup, a):
		elements = set()
		for h in subgroup:
			elements |= set([self.operation(a, h)])
		return tuple(sorted(list(elements)))

	'''
	Compute the right coset for the given subgroup of G and the given element a.
	'''
	def right_coset(self, subgroup, a):
		elements = set()
		for h in subgroup:
			elements |= set([self.operation(h, a)])
		return tuple(sorted(list(elements)))

	'''
	Compute all left cosets for the given subgroup of G.
	'''
	def left_cosets(self, subgroup):
		return tuple(set([self.left_coset(subgroup, a) for a in self.elements]))

	'''
	Compute all right cosets for the given subgroup of G.
	'''
	def right_cosets(self, subgroup):
		return tuple(set([self.right_coset(subgroup, a) for a in self.elements]))

	'''
	Check if the given set H is a subgroup of G.
	'''
	def is_subgroup(self, H):
		if not self.identity in H:
			return False
		for a, b in product(H, repeat=2):
			if not self.operation(a, self.inverses[b]) in H:
				return False
		return True

	'''
	Check if the given set N is a normal divisor of G.
	'''
	def is_normal_divisor(self, N):
		if not self.is_subgroup(N):
			return False
		for g in self.elements:
			g_ = self.inverses[g]
			for h in N:
				n = self.operation(g, self.operation(h, g_))
				if not n in N:
					return False
		return True

	'''
	Find the generators of G given the limits maxN and maxPower.
	'''
	def generators(self, maxN=None, maxPower=40):
		if maxN == None:
			maxN = len(self.elements)
		for i in range(maxN):
			n = i + 1
			gens = product(self.elements, repeat=n)
			for gen in gens:
				elements = set()
				for g in gen:
					for p in range(maxPower * 2):
						elements |= set([self.powerOf(g, p - maxPower)])
				if len(elements) == len(self.elements):
					yield gen


	'''
	Create a subgroup of H with the same operation as G.
	'''
	def subgroup(self, H):
		return Group(H, self.fn)

	'''
	Compute all subgroups of G.
	'''
	def subgroups(self):
		return map(self.subgroup, filter(self.is_subgroup, powerset(self.elements)))

	'''
	Compute all normal divisors of G.
	'''
	def normal_divisors(self):
		return map(self.subgroup, filter(self.is_normal_divisor, powerset(self.elements)))

	'''
	Compute the order of a.
	'''
	def order(self, a):
		n = 1
		x = a
		while x != self.identity:
			x = self.operation(x, a)
			n += 1
		return n

	'''
	Compute the order for all elements in G.
	'''
	def orders(self):
		return [(a, self.order(a)) for a in self.elements]

	'''
	Check if a is central in G.
	'''
	def is_central(self, a):
		for x in self.elements:
			ax = self.operation(a, x)
			xa = self.operation(x, a)
			if ax != xa:
				return False
		return True

	'''
	Compute the center of G.
	'''
	def center(self):
		return self.subgroup([a for a in self.elements if self.is_central(a)])

	'''
	Compute the product group of G with some other group H.
	'''
	def product(self, H):
		return Group(list(itertools.product(self.elements, repeat=2)), lambda a, b: (self.fn(a[0], b[0]), H.fn(a[1], b[1])))

	'''
	Compute the factorial group G/N.
	'''
	def factorize(self, N):
		GN = {}
		for g in self.elements:
			gn = self.left_coset(N.elements, g)
			if not gn in GN:
				GN[gn] = g
		return Group(sorted(list(GN.values())), lambda x, y: GN[self.left_coset(N.elements, self.fn(x, y))])

	'''
	Check if the given operation is a morphism from G to another group _G.
	'''
	def is_morphism(self, G_, fn=lambda x: x):
		for a, b in itertools.product(self.elements, repeat=2):
			if fn(self.operation(a, b)) != G_.operation(fn(a), fn(b)):
				return False
		return True

'''
GroupActor class.
'''
class GroupActor:
	def __init__(self, G, X, fn):
		self.G = G
		self.X = X
		self.fn = fn

	def action(self, g, x):
		return self.fn(g, x)

	def is_valid(self):
		for x in self.X:
			if self.action(self.G.identity, x) != x:
				return False
		for g, h in itertools.product(self.G.elements, repeat=2):
			for x in self.x:
				if self.action(self.G.operation(g, h), x) != self.action(g, self.action(h, x)):
					return False
		return True
