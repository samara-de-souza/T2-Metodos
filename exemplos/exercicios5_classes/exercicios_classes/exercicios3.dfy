type T = int // para demonstração, mas poderia ser qualquer tipo

class {:autocontracts} Deque
{
    // Abstração
    ghost var Conteudo: seq<T>
    ghost const Capacidade: nat

    // Implementação 
    const a: array<T> 
    const cap: nat
    var cauda: nat

    ghost predicate Valid()
    {
      cap > 0 &&
      a.Length == cap &&
      0 <= cauda <= cap &&
      Conteudo == a[0..cauda] &&
      Capacidade == cap
    }
 
    constructor (c: nat)
      requires c > 0
      ensures Conteudo == []
      ensures Capacidade == c
    {
      a := new T[c];
      cap := c;
      cauda := 0;
      Conteudo := [];
      Capacidade := c;
    }

    //Predicado que pode ser utilizado como um método, gerando código executável
    predicate isEmpty()
      ensures isEmpty() <==> Conteudo == []
    {
      cauda == 0
    }
    
    //Predicado que pode ser utilizado como um método, gerando código executável
    predicate isFull()
      ensures isFull() <==> |Conteudo| == Capacidade
    {
      cauda == cap
    }

    //Função que pode ser utilizada como um método, gerando código executável
    function front() : T
      requires !isEmpty()
      ensures front() == Conteudo[0]
    {
      a[0]
    }

    //Função que pode ser utilizada como um método, gerando código executável
    function back() : T
      requires !isEmpty()
      ensures back() == Conteudo[|Conteudo| - 1]
    {
      a[cauda-1]
    }

    method push_back(e : T)
      requires !isFull()
      ensures Conteudo == old(Conteudo) + [e]
    {
      a[cauda] := e;
      cauda := cauda + 1;
      Conteudo := Conteudo + [e];
    }

    method pop_back() returns (e:T)
      requires !isEmpty()
      ensures e == old(Conteudo[|Conteudo| - 1])
      ensures Conteudo == old(Conteudo[..|Conteudo|-1])
    {
      cauda := cauda - 1;
      e := a[cauda];
      Conteudo := Conteudo[..cauda];
    }

    method push_front(e : T)
      requires !isFull()
      ensures Conteudo == [e] + old(Conteudo) 
    {
      forall i | 0 <= i < cauda
      {
        a[cauda - i] := a[cauda - i - 1];
      }
      a[0] := e;
      cauda := cauda + 1;
      Conteudo := [e] + Conteudo;
    }

    method pop_front() returns (e:T)
      requires !isEmpty()
      ensures e == old(Conteudo[0])
      ensures Conteudo == old(Conteudo[1..])
    {
      e := a[0];
      cauda := cauda - 1;
      forall i | 0 <= i < cauda
      {
        a[i] := a[i+1];
      }
      Conteudo := a[0..cauda];
    }
}

method Main()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    var e := q.pop_back();
    assert e == 3;
    assert q.front() == 2;
    assert q.back() == 1;
    e := q.pop_front();
    assert e == 2;
    assert q.front() == 1;
    assert q.back() == 1;
    e := q.pop_front();
    assert e == 1;
    assert q.isEmpty();
}
