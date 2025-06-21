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
        // pós-condições
        ensures |reverseSeq(s)| == |s|
        ensures forall i :: 0 <= i < |s| ==> reverseSeq(s)[i] == s[|s|-1-i]
    {
        if |s| == 0 then [] else [s[|s|-1]] + reverseSeq(s[..|s|-1])
    }

    // Construtor
    constructor()
        // pós-condições
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
    method add(e: int) 
        // cláusula frame
        modifies this, a
    {
        if top == a.Length {
            var b := new int[2 * a.Length];
            var i := 0;
            while i < a.Length
                // invariantes do laço
                invariant 0 <= i <= a.Length
                // variante de terminação
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
        // pré-condições
        requires Valid()
        requires top > 0
        // cláusula frame
        modifies this, Repr, a
        // pós-condições
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
        // pré-condições
        requires Valid()
        requires top > 0
        // pós-condições
        ensures e == Content[|Content| - 1]
        ensures Valid()
    {
        e := a[top - 1];
    }

    // Verificar se está vazio
    method isEmpty() returns (b: bool)
        requires Valid()
        ensures b <==> (top == 0)  // pós-condição
        ensures Valid()
    {
        b := (top == 0);
    }

    // Quantidade de elementos
    method howManyStored() returns (n: nat)
        requires Valid()
        ensures n == top  // pós-condição
        ensures Valid()
    {
        n := top;
    }
    
    // Novo método: inverte a pilha in-place
    method reverse()
        requires Valid()              // pré-condição
        modifies this, a              // frame
        // (pós-condições omitidas)
    {
        var i := 0;
        while i < top / 2
            // invariantes do laço
            invariant 0 <= i <= top / 2
            invariant top <= a.Length
            // frame interno do laço
            modifies a
            // variante de terminação
            decreases top / 2 - i
        {
            var j := top - 1 - i;
            var temp := a[i];
            a[i] := a[j];
            a[j] := temp;
            i := i + 1;
        }
        Content := a[0..top];
    }
}

// Main externo com asserts estilo exemplo
/* method main()
{
    var s := new Stack();
    s.add(1);
    s.add(2);
    s.add(3);
    s.reverse();
    var e := s.remove();
    var vazio := s.isEmpty();
    var qtd := s.howManyStored();
    var topo := s.peek();
    s.add(4);
    s.add(5);
    s.reverse();
    var e2 := s.remove();
    var e3 := s.remove();
    var e4 := s.remove();
    var vazio2 := s.isEmpty();
    var qtd2 := s.howManyStored();
    var topo2 := s.peek();
    s.add(6);
    s.add(7);
    s.reverse();
    var e5 := s.remove();
    var e6 := s.remove();
    var e7 := s.remove();
    var vazio3 := s.isEmpty();
    var qtd3 := s.howManyStored();
    var topo3 := s.peek();
}