#
# Graph with SCC support for grouping mutually related kinds
#

import graphlib


class Graph:
	"""Graph with SCC support"""

	def __init__(self):
		self.graph = {}

		self.indices = {}
		self.lowlink = {}
		self.next_index = 0
		self.stack = []
		self.sccs = []

	def add_vertex(self, vertex):
		"""Add empty vertex"""
		self.graph.setdefault(vertex, set())

	def add_edge(self, origin, dest):
		"""Add an edge to the graph"""
		self.graph.setdefault(origin, set()).add(dest)
		self.graph.setdefault(dest, set())

	def _scc(self, v):
		"""Explore from a vertex to find SCCs"""

		if v in self.indices:
			return

		self.indices[v] = self.next_index
		self.lowlink[v] = self.next_index
		self.stack.append(v)
		self.next_index += 1

		for w in self.graph[v]:
			if w not in self.indices:
				self._scc(w)
				self.lowlink[v] = min(self.lowlink[v], self.lowlink[w])
			elif w in self.stack:
				self.lowlink[v] = min(self.lowlink[v], self.indices[w])

		# This is a new connected component
		if self.indices[v] == self.lowlink[v]:
			w = self.stack.pop()
			scc = {w}
			while w != v:
				w = self.stack.pop()
				scc.add(w)
			self.sccs.append(scc)

	def topological_scc(self):
		"""Calculate a topological ordering of the SCCs of this graph"""

		# (1) Tarjan's SCC algorithm to calculate the components

		self.next_index = 0
		self.indices = {}
		self.lowlink = {}
		self.stack = []
		self.sccs = []

		for v in self.graph.keys():
			self._scc(v)

		# (2) Calculate a topological ordering with graphlib
		vertex2scc = {v: i for i, scc in enumerate(self.sccs) for v in scc}
		# New graph of SCCs to calculate their topological ordering
		new_graph = {k: {vertex2scc[w] for v in scc for w in self.graph[v]} - {k}
		             for k, scc in enumerate(self.sccs)}
		new_graph = graphlib.TopologicalSorter(new_graph)

		return [self.sccs[k] for k in new_graph.static_order()]

	def items(self):
		"""Iterate over the nodes of the graph"""
		return self.graph.items()

	def __repr__(self):
		return f'Graph({self.graph})'
