class FilaNat
{
  //Implementação
  var a: array<nat>
  var cauda: nat
  //Abstração
  ghost var Conteudo: seq<nat>
  ghost var Repr: set<object>

  //Invariante de classe
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    a in Repr &&
    a.Length != 0 &&
    0 <= cauda <= a.Length &&
    Conteudo == a[0..cauda]
  }

  constructor ()
    ensures Valid() && fresh(Repr)
    ensures Conteudo == []
  {
    a := new nat[5];
    cauda := 0;
    Conteudo := [];
    Repr := {this, a};
  }

  function Quantidade():nat
    requires Valid()
    reads Repr
    ensures Quantidade() == |Conteudo|
  {
    cauda
  }

  method Enfileira(e:nat)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Conteudo == old(Conteudo) + [e]
  {
    if cauda == a.Length
    {
      var b := new nat[2 * a.Length];
      forall i | 0 <= i < a.Length
      {
        b[i] := a[i];
      }
      Repr := Repr - {a};
      a := b;
      Repr := Repr + {b};
    }
    a[cauda] := e;
    cauda := cauda + 1;
    Conteudo := Conteudo + [e];
  }

  method Desenfileira() returns (e:nat)
    requires Valid()
    requires |Conteudo| > 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures e == old(Conteudo[0])
    ensures Conteudo == old(Conteudo)[1..]
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
  var fila := new FilaNat();
  fila.Enfileira(1);
  fila.Enfileira(2);
  assert fila.Conteudo == [1,2];
  var q := fila.Quantidade();
  assert q == 2;
  var e := fila.Desenfileira();
  assert e == 1;
  assert fila.Conteudo == [2];
}