# Implementation of Trees and Graph Algorithms for Campus Navigation and Data Management.

from dataclasses import dataclass
import heapq

@dataclass
class Building:
    id: int; name: str; loc: str
    def __repr__(self): return f"{self.id}:{self.name}"

class BSTNode:
    def __init__(self,b): self.b=b; self.l=None; self.r=None
class BST:
    def __init__(self): self.root=None
    def insert(self,b):
        def ins(n):
            if not n: return BSTNode(b)
            if b.id < n.b.id: n.l = ins(n.l)
            elif b.id > n.b.id: n.r = ins(n.r)
            return n
        self.root = ins(self.root)
    def inorder(self):
        res=[]
        def go(n):
            if not n: return
            go(n.l); res.append(n.b); go(n.r)
        go(self.root); return res
    def search(self,key):
        n=self.root
        while n:
            if key==n.b.id: return n.b
            n = n.l if key < n.b.id else n.r
        return None
    def height(self):
        def h(n): return 0 if not n else 1+max(h(n.l),h(n.r))
        return h(self.root)

class AVLNode:
    def __init__(self,b): self.b=b; self.l=None; self.r=None; self.h=1
class AVL:
    def __init__(self): self.root=None
    def _h(self,n): return n.h if n else 0
    def _bf(self,n): return self._h(n.l)-self._h(n.r) if n else 0
    def _rotR(self,y):
        x=y.l; y.l=x.r; x.r=y
        y.h=1+max(self._h(y.l),self._h(y.r)); x.h=1+max(self._h(x.l),self._h(x.r))
        return x
    def _rotL(self,x):
        y=x.r; x.r=y.l; y.l=x
        x.h=1+max(self._h(x.l),self._h(x.r)); y.h=1+max(self._h(y.l),self._h(y.r))
        return y
    def insert(self,b):
        def ins(n):
            if not n: return AVLNode(b)
            if b.id < n.b.id: n.l = ins(n.l)
            elif b.id > n.b.id: n.r = ins(n.r)
            else: return n
            n.h = 1 + max(self._h(n.l), self._h(n.r))
            bf = self._bf(n)
            if bf>1 and b.id < n.l.b.id: return self._rotR(n)
            if bf<-1 and b.id > n.r.b.id: return self._rotL(n)
            if bf>1 and b.id > n.l.b.id: n.l = self._rotL(n.l); return self._rotR(n)
            if bf<-1 and b.id < n.r.b.id: n.r = self._rotR(n.r); return self._rotL(n)
            return n
        self.root = ins(self.root)
    def inorder(self):
        res=[]
        def go(n):
            if not n: return
            go(n.l); res.append(n.b); go(n.r)
        go(self.root); return res
    def height(self): return self.root.h if self.root else 0

class Graph:
    def __init__(self, nodes):
        self.nodes = sorted(nodes)
        self.idx = {v:i for i,v in enumerate(self.nodes)}
        self.adj = {v:[] for v in self.nodes}
        n=len(self.nodes)
        self.mat = [[float('inf')]*n for _ in range(n)]
        for i in range(n): self.mat[i][i]=0
    def add_edge(self,u,v,w=1,und=True):
        self.adj[u].append((v,w))
        if und: self.adj[v].append((u,w))
        i,j=self.idx[u],self.idx[v]; self.mat[i][j]=w
        if und: self.mat[j][i]=w
    def bfs(self,s):
        vis={s}; q=[s]; order=[]
        while q:
            u=q.pop(0); order.append(u)
            for v,_ in self.adj[u]:
                if v not in vis: vis.add(v); q.append(v)
        return order
    def dfs(self,s):
        vis=set(); order=[]
        def d(u):
            vis.add(u); order.append(u)
            for v,_ in self.adj[u]:
                if v not in vis: d(v)
        d(s); return order
    def dijkstra(self,src):
        dist={v:float('inf') for v in self.nodes}; dist[src]=0
        pq=[(0,src)]
        while pq:
            d,u=heapq.heappop(pq)
            if d>dist[u]: continue
            for v,w in self.adj[u]:
                nd=d+w
                if nd<dist[v]: dist[v]=nd; heapq.heappush(pq,(nd,v))
        return dist

class UF:
    def __init__(self,els): self.p={e:e for e in els}; self.r={e:0 for e in els}
    def find(self,x):
        if self.p[x]!=x: self.p[x]=self.find(self.p[x])
        return self.p[x]
    def union(self,a,b):
        ra,rb=self.find(a),self.find(b)
        if ra==rb: return False
        if self.r[ra]<self.r[rb]: self.p[ra]=rb
        elif self.r[rb]<self.r[ra]: self.p[rb]=ra
        else: self.p[rb]=ra; self.r[ra]+=1
        return True
def kruskal(nodes,edges):
    uf=UF(nodes); edges=sorted(edges,key=lambda x:x[2])
    mst=[]; total=0
    for u,v,w in edges:
        if uf.union(u,v): mst.append((u,v,w)); total+=w
    return mst,total

class ENode:
    def __init__(self,v): self.v=v; self.l=None; self.r=None
def build_expr(postfix):
    stk=[]; ops=set(['+','-','*','/','^'])
    for t in postfix:
        if t in ops:
            r=stk.pop(); l=stk.pop(); n=ENode(t); n.l=l; n.r=r; stk.append(n)
        else:
            stk.append(ENode(t))
    return stk[-1]
def eval_expr(node,vars={}):
    if not node.l and not node.r:
        try: return float(node.v)
        except: return float(vars.get(node.v,0))
    a=eval_expr(node.l,vars); b=eval_expr(node.r,vars)
    if node.v=='+': return a+b
    if node.v=='-': return a-b
    if node.v=='*': return a*b
    if node.v=='/': return a/b
    if node.v=='^': return a**b

def demo():
    B = [Building(10,"Academic","Main"), Building(20,"Library","Center"),
         Building(30,"Cafeteria","Food"), Building(40,"Sports","East"), Building(50,"Hostel","North")]
    # Trees
    bst = BST(); avl=AVL()
    for b in B: bst.insert(b); avl.insert(b)
    print("BST inorder:", bst.inorder())
    print("BST height:", bst.height(), " | AVL height:", avl.height())
    print("Search 30 in BST ->", bst.search(30))

    nodes=[b.id for b in B]; G=Graph(nodes)
    edges=[(10,20,5),(10,30,3),(20,30,2),(30,40,7),(40,50,4),(20,50,12)]
    for u,v,w in edges: G.add_edge(u,v,w)
    print("Adj list:", G.adj)
    print("BFS from 10:", G.bfs(10))
    print("DFS from 10:", G.dfs(10))
    print("Dijkstra from 10:", G.dijkstra(10))

    mst,total = kruskal(nodes,edges)
    print("MST:", mst, "Total:", total)

    post=["units","rate","*","fixed","+"]
    root=build_expr(post)
    print("Bill:", eval_expr(root, {"units":350,"rate":5.5,"fixed":50}))

if __name__=="__main__":
    demo()