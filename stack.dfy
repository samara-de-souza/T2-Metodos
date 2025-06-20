// integrantes: Mykelly Barros e Samara Tavares

class Stack {
    // Implementação
    var a: array<int>
    var top: nat

    // Abstração
    ghost var Content: seq<int>
    ghost var Repr: set<object>

    // Invariante de classe
    ghost predicate Valid()
        reads this, Repr, a
        ensures Valid() ==> this in Repr
    {
        this in Repr &&
        a in Repr &&
        a.Length != 0 &&
        0 <= top <= a.Length &&
        Content == a[0..top]
    }

    // Função fantasma para reverter sequência
    ghost function reverseSeq(s: seq<int>): seq<int>
        ensures |reverseSeq(s)| == |s|
        ensures forall i :: 0 <= i < |s| ==> reverseSeq(s)[i] == s[|s|-1-i]
    {
        if |s| == 0 then [] else [s[|s|-1]] + reverseSeq(s[..|s|-1])
    }

    // Construtor
    constructor()
        ensures Valid() 
        ensures Content == []
        ensures top == 0
        ensures this in Repr && a in Repr
    {
        a := new int[10];
        top := 0;
        Content := [];
        Repr := {this, a};
    }

    // Adicionar elemento
    method add(e: int) modifies this, a
    {
        if top == a.Length {
            var b := new int[2 * a.Length];
            var i := 0;
            while i < a.Length
                invariant 0 <= i <= a.Length
                decreases a.Length - i
            {
                if i < a.Length && i < b.Length {
                    b[i] := a[i];
                }
                i := i + 1;
            }
            a := b;
        }
        if top < a.Length {
            a[top] := e;
            top := top + 1;
        }
    }

    // Remover elemento
    method remove() returns (e: int)
        requires Valid()
        requires top > 0
        modifies this, Repr, a
        ensures Valid() && fresh(Repr - old(Repr))
        ensures e == old(Content)[|old(Content)| - 1]
        ensures Content == old(Content)[0..|old(Content)| - 1]
        ensures top == old(top) - 1
    {
        top := top - 1;
        e := a[top];
        Content := a[0..top];
    }

    // Ver topo
    method peek() returns (e: int)
        requires Valid()
        requires top > 0
        ensures e == Content[|Content| - 1]
        ensures Valid()
    {
        e := a[top - 1];
    }

    // Verificar se está vazio
    method isEmpty() returns (b: bool)
        requires Valid()
        ensures b <==> (top == 0)
        ensures Valid()
    {
        b := (top == 0);
    }

    // Quantidade de elementos
    method howManyStored() returns (n: nat)
        requires Valid()
        ensures n == top
        ensures Valid()
    {
        n := top;
    }

    // Reverter pilha (retorna nova pilha, não altera a original)
    method reverse() returns (rev: Stack)
        requires Valid()
        ensures rev.Valid()
        ensures rev.Content == reverseSeq(Content)
        ensures rev.top == top
        ensures rev != this
    {
        rev := new Stack();
        var i := 0;
        while i < top
            invariant 0 <= i <= top
            invariant rev.top == i
            invariant rev.Content == reverseSeq(Content)[..i]
            decreases top - i
        {
            rev.add(a[top - 1 - i]);
            i := i + 1;
        }
    }

    // União de duas pilhas (retorna nova pilha, não altera as originais)
    method union(p2: Stack) returns (result: Stack)
        requires Valid()
        requires p2.Valid()
        ensures result.Valid()
        ensures result.Content == Content + p2.Content
        ensures result.top == top + p2.top
        ensures result != this && result != p2
        ensures Content == old(Content) && p2.Content == old(p2.Content)
    {
        result := new Stack();
        var i := 0;
        while i < top
            invariant 0 <= i <= top
            invariant result.top == i
            invariant result.Content == Content[..i]
            decreases top - i
        {
            result.add(a[i]);
            i := i + 1;
        }
        i := 0;
        while i < p2.top
            invariant 0 <= i <= p2.top
            invariant result.top == top + i
            invariant result.Content == Content + p2.Content[..i]
            decreases p2.top - i
        {
            result.add(p2.a[i]);
            i := i + 1;
        }
    }
}