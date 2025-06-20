// palavra contém uma string
// remover p caracteres a partir da posição ini até fim
method Delete(palavra:array<char>, ini:nat, fim:nat, p:nat)
  requires fim <= palavra.Length
  requires ini+p <= fim
  modifies palavra
  ensures palavra[..ini] == old(palavra[..ini])
  ensures palavra[ini..fim-p] == old(palavra[ini+p..fim])
{
    var i:nat := 0;
    while i < fim-(ini+p)
      invariant i <= fim-(ini+p)
      invariant ini+p+i >= ini+i 
      invariant palavra[..ini] == old(palavra[..ini])
      invariant palavra[ini..ini+i] == old(palavra[ini+p..ini+p+i])
      invariant palavra[ini+i..fim] == old(palavra[ini+i..fim]) // futuro é intocável
    { 
        palavra[ini+i] := palavra[ini+p+i];
        i := i+1;
    }
}