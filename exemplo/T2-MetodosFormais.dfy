// Nomes: Ana Carolina Xavier, Érico Bis, Gabriel Piazenski, Gustavo Willian e Rubens Montanha

class Conjunto 
  {
  // Implementação
  var elementos: array<int>
  var count: nat

  // Abstração
  ghost var abstractSet: set<int>

  // Invariante de Classe
  ghost predicate Valid()
    reads this
    reads elementos
  {
    count >= 0
    && count == elementos.Length
    && count == |abstractSet|
    && (forall i, j :: (0 <= i < j < count ==> elementos[i] != elementos[j]))
    && (forall n :: n in abstractSet <==> (exists i :: 0 <= i < count && elementos[i] == n))
    && (forall i :: (0 <= i < count ==> elementos[i] in abstractSet))
  }

  constructor()
    ensures Valid()
    ensures count == 0
    ensures count == elementos.Length
  {
    count := 0;
    elementos := new int[0];

    abstractSet := {};
  }

  function ContemElemento(n: int): bool
    requires Valid()
    ensures ContemElemento(n) == (n in abstractSet)
    reads this
    reads elementos
  {
    exists i :: 0 <= i < GetTamanho() && elementos[i] == n
  }

  function EstaVazio() :bool
    requires Valid()
    ensures EstaVazio() == (|abstractSet| == 0)
    reads this
    reads elementos
  {
    count == 0
  }

  function GetTamanho() : nat
    requires Valid()
    ensures GetTamanho() == |abstractSet|
    reads this
    reads elementos
  {
    count
  }

  method Adiciona(n: int)
  requires Valid()
  requires forall i :: 0 <= i < count ==> ContemElemento(elementos[i])
  requires !ContemElemento(n)
  ensures Valid()
  ensures count == old(count) + 1
  ensures ContemElemento(n)
  ensures forall i :: 0 <= i < count ==> ContemElemento(elementos[i])
  modifies this
  {
    var t_elementos := new int[count + 1];

    var i := 0;

    assert |abstractSet| == count;

    while(i < count)
      invariant 0 <= i <= count
      invariant count == t_elementos.Length - 1
      invariant count == elementos.Length
      invariant forall j :: 0 <= j < i ==> t_elementos[j] == elementos[j]
      invariant forall j :: 0 <= j < count ==> elementos[j] != n
      invariant forall j, k :: 0 <= j < k < count ==> elementos[j] != elementos[k]
      invariant forall j, k :: 0 <= j < k < i ==> t_elementos[j] != t_elementos[k]
    {
      t_elementos[i] := elementos[i];

      i := i + 1;
    }

    t_elementos[count] := n;

    count := count + 1;
    elementos := t_elementos;

    abstractSet := {};

    assert exists i :: 0 <= i < count && elementos[i] == n;

    for i := 0 to |elementos[..]|
      invariant forall j, k :: 0 <= j < k < count ==> elementos[j] != elementos[k]
      invariant forall e :: e in elementos[..i] <==> e in abstractSet
      invariant |elementos[..i]| == |abstractSet|
      invariant exists k :: 0 <= k < count && elementos[k] == n
    {
      abstractSet := abstractSet + {elementos[i]};
    }

    assert exists i :: 0 <= i < count && elementos[i] == n;
  }

  method Remove(n: int)
    requires Valid()
    requires exists i :: (0 <= i < count ==> elementos[i] == n)
    requires count > 0
    ensures Valid()
    ensures count == old(count) - 1
    ensures elementos.Length == old(elementos).Length - 1
    ensures forall e :: e in abstractSet ==> exists i :: 0 <= i < count && elementos[i] == e
    modifies this, elementos
  {
    var r_pos := 0;

    var i := 0;

    while (i < count)
      invariant 0 <= i <= count
      invariant forall j :: 0 <= j < i ==> elementos[j] != n
    {
      if (elementos[i] == n) {
        r_pos := i;
        break;
      }
      i := i + 1;
    }

    var t_elemento := elementos[r_pos];
    elementos[r_pos] := elementos[count - 1];
    elementos[count - 1] := t_elemento;

    var t_elementos := new int[count - 1];

    i := 0;

    while (i < count - 1)
      invariant 0 <= i < count
      invariant count == t_elementos.Length + 1
      invariant count == elementos.Length
      invariant forall j :: 0 <= j < i ==> t_elementos[j] == elementos[j]
      invariant forall j, k :: 0 <= j < k < count ==> elementos[j] != elementos[k]
      invariant forall j, k :: 0 <= j < k < i ==> t_elementos[j] != t_elementos[k]
    {
      t_elementos[i] := elementos[i];

      i := i + 1;
    }

    elementos := t_elementos;
    count := count - 1;

    abstractSet := abstractSet - {n};

  }


  method Union(c: Conjunto) returns (r: Conjunto)
    requires Valid()
    requires c.Valid()
    ensures r.Valid()
    ensures forall i, j :: (0 <= i < j < r.count ==> r.elementos[i] != r.elementos[j])
    // ensures forall i :: (0 <= i < count ==> r.ContemElemento(elementos[i])) && forall i :: (0 <= i < c.count ==> r.ContemElemento(c.elementos[i]))
  {
    var conjunto := new Conjunto();

    var i := 0;

    assert conjunto.EstaVazio() == true;

    while(i < GetTamanho())
      invariant 0 <= i <= GetTamanho()
      invariant conjunto.Valid()
      invariant forall j, k :: 0 <= j < k < count ==> elementos[j] != elementos[k]
    {
      if (!conjunto.ContemElemento(elementos[i])) {
        conjunto.Adiciona(elementos[i]);
      }
      i := i + 1;
    }

    i := 0;
    while (i < c.count)
      invariant 0 <= i <= c.count
      invariant conjunto.Valid()
      invariant forall j, k :: 0 <= j < k < c.count ==> c.elementos[j] != c.elementos[k]
    {
      if (!conjunto.ContemElemento(c.elementos[i])) {
        conjunto.Adiciona(c.elementos[i]);
      }
      i := i + 1;
    }

    return conjunto;
  }

  method Intersection(c: Conjunto) returns (r: Conjunto)
    requires Valid()
    requires c.Valid()
    ensures r.Valid()
    ensures forall i, j :: (0 <= i < j < r.count ==> r.elementos[i] != r.elementos[j])
  {
    var conjunto := new Conjunto();

    var i := 0;
    while(i < count)
      invariant 0 <= i <= count
      invariant conjunto.Valid()
      invariant forall j, k :: 0 <= j < k < count ==> elementos[j] != elementos[k]
    {
      var j := 0;
      while (j < c.count)
        invariant 0 <= j <= c.count
        invariant conjunto.Valid()
        invariant forall k, l :: 0 <= k < l < c.count ==> c.elementos[k] != c.elementos[l]
      {
        if (elementos[i] == c.elementos[j] && !conjunto.ContemElemento(elementos[i])) {
          conjunto.Adiciona(elementos[i]);
          break;
        }
        j := j + 1;
      }

      i := i + 1;
    }

    return conjunto;
  }
}
  


method Main()
{
  var c1 := new Conjunto();

  assert c1.EstaVazio() == true;
  assert c1.GetTamanho() == 0;

  c1.Adiciona(1);

  assert c1.EstaVazio() == false;
  assert c1.GetTamanho() == 1;
  assert c1.ContemElemento(1) == true;

  if (!c1.ContemElemento(2)) {
    c1.Adiciona(2);

    assert c1.EstaVazio() == false;
    assert c1.GetTamanho() == 2;

    if (!c1.ContemElemento(3)) {
    c1.Adiciona(3);

    assert c1.EstaVazio() == false;
    assert c1.GetTamanho() == 3;

    var c3 := new Conjunto();
  }

  }

  var c2 := new Conjunto();

  assert c2.EstaVazio() == true;
  assert c2.GetTamanho() == 0;

}