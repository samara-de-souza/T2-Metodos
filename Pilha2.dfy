class Pilha {
  var elementos: array<int>
  var tamanho: int

  ghost var Repr: set<object>

  predicate Valid()
    reads this, Repr
  {
    0 <= tamanho && tamanho <= elementos.Length
  }

  constructor(capacidade: int)
    requires capacidade > 0
    ensures Valid()
  {
    elementos := new int[capacidade];
    tamanho := 0;
    Repr := {this};
  }

  method Empilhar(valor: int)
    requires tamanho < elementos.Length 
    modifies this.elementos
    ensures Valid()
  {
    elementos[tamanho] := valor;
    tamanho := tamanho + 1;
    assert Valid();
  }

  /* method Desempilhar() returns (valor: int)
  requires tamanho > 0
  modifies this.elementos/* , this.tamanho */
  ensures Valid()
  {
    /* assert tamanho > 0; */
    valor := elementos[tamanho - 1];
    tamanho := tamanho - 1;
  }

  method Topo() returns (valor: int)
    requires tamanho > 0
    modifies this.elementos
    ensures Valid()
  {
    valor := elementos[tamanho - 1];
  }

  method EstaVazia() returns (result: bool)
    ensures Valid()
  {
    result := (tamanho == 0);
  }

  method Tamanho() returns (result: int)
    ensures Valid()
  {
    result := tamanho;
  }

  method Inverter()
    ensures Valid()
  {
    var i := 0;
    var j := tamanho - 1;
    assert 0 <= i <= j < tamanho;
    while i < j
      invariant 0 <= i <= j < tamanho 
    {
      var temp := elementos[i];
      elementos[i] := elementos[j];
      elementos[j] := temp;
      i := i + 1;
      j := j - 1;
    }
  }

  method Main()
  {
    var pilha1 := new Pilha(5);
    pilha1.Empilhar(10);
    pilha1.Empilhar(20);
    pilha1.Empilhar(30);

    var pilha2 := new Pilha(5);
    pilha2.Empilhar(40);
    pilha2.Empilhar(50);
  } */
}