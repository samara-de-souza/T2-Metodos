class Pilha {
    // Implementação
    var a: array<int>
    var topo: nat

    // Abstração
    ghost var Conteudo: seq<int>
    ghost var Repr: set<object>

    // Invariante de classe
    ghost predicate Valid()
        reads this, Repr, a
        ensures Valid() ==> this in Repr
    {
        this in Repr &&
        a in Repr &&
        a.Length != 0 &&
        0 <= topo <= a.Length &&
        Conteudo == a[0..topo]
    }

    constructor()
        ensures Valid() && fresh(Repr)
        ensures Conteudo == []
    {
        a := new int[5];
        topo := 0;
        Conteudo := [];
        Repr := {this, a};
    }

    function Quantidade(): nat
        requires Valid()
        reads a, Repr
        ensures Quantidade() == |Conteudo|
    {
        topo
    }

    method Empilha(e: int)
        requires Valid()
        modifies this, Repr, a
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Conteudo == old(Conteudo) + [e]
    {
        if topo == a.Length {
            var b := new int[2 * a.Length];
            forall i | 0 <= i < a.Length {
                b[i] := a[i];
            }
            Repr := Repr - {a};
            a := b;
            Repr := Repr + {b};
        }
        a[topo] := e;
        topo := topo + 1;
        Conteudo := Conteudo + [e];
    }

    method Desempilha() returns (e: int)
        requires Valid()
        requires |Conteudo| > 0
        modifies this, Repr, a
        ensures Valid() && fresh(Repr - old(Repr))
        ensures e == old(Conteudo)[|old(Conteudo)|-1]
        ensures Conteudo == old(Conteudo)[..|old(Conteudo)|-1]
    {
        topo := topo - 1;
        e := a[topo];
        Conteudo := a[0..topo];
    }

    function Topo(): int
        requires Valid()
        requires |Conteudo| > 0
        reads a, Repr
        ensures Topo() == Conteudo[|Conteudo|-1]
    {
        a[topo-1]
    }

    predicate Vazia()
        requires Valid()
        reads this
        ensures Vazia() <==> topo == 0
    {
        topo == 0
    }

    function SeqRev(s: seq<int>): seq<int> {
        if |s| == 0 then [] else [s[|s|-1]] + SeqRev(s[..|s|-1])
    }

    method Inverte()
        requires Valid()
        modifies this, Repr, a
        ensures Valid() && fresh(Repr - old(Repr))
        ensures Conteudo == SeqRev(old(Conteudo))
    {
        var n := topo;
        var i := 0;
        while i < n/2
            invariant 0 <= i <= n/2
            invariant Valid()
            invariant forall j | 0 <= j < n :: (j < i || j >= n-i ==> a[j] == old(Conteudo)[n-1-j])
            invariant forall j | i <= j < n-i ==> a[j] == old(Conteudo)[j]
        {
            var tmp := a[i];
            a[i] := a[n-1-i];
            a[n-1-i] := tmp;
            i := i + 1;
        }
        Conteudo := a[0..topo];
    }

    method ObterElemento(i: nat) returns (e: int)
        requires Valid()
        requires i < topo
        ensures e == a[i]
    {
        e := a[i];
    }

    static method EmpilhaPilhas(p1: Pilha, p2: Pilha) returns (p: Pilha)
        requires p1.Valid() && p2.Valid()
        ensures p.Valid()
        ensures p.Conteudo == p1.Conteudo + p2.Conteudo
    {
        p := new Pilha();
        var i := 0;
        while i < p1.topo
            invariant 0 <= i <= p1.topo
            invariant p.Valid()
            invariant p.Conteudo == p1.Conteudo[..i]
        {
            var v := p1.ObterElemento(i);
            p.Empilha(v);
            i := i + 1;
        }
        i := 0;
        while i < p2.topo
            invariant 0 <= i <= p2.topo
            invariant p.Valid()
            invariant p.Conteudo == p1.Conteudo + p2.Conteudo[..i]
        {
            var v := p2.ObterElemento(i);
            p.Empilha(v);
            i := i + 1;
        }
    }
}

method Main()
{
    var p := new Pilha();
    assert p.Vazia();
    p.Empilha(10);
    p.Empilha(20);
    assert p.Quantidade() == 2;
    assert p.Topo() == 20;
    var x := p.Desempilha();
    assert x == 20;
    assert p.Quantidade() == 1;
    p.Empilha(30);
    p.Empilha(40);
    p.Inverte();
    assert p.Quantidade() == 3;
    var p2 := new Pilha();
    p2.Empilha(100);
    var p3 := Pilha.EmpilhaPilhas(p, p2);
    assert p3.Quantidade() == 4;
    assert p3.Topo() == 100;
}
