// palavra contém uma string
// remover p caracteres a partir da posição ini até fim
method Delete(palavra:array<char>, ini:nat, fim:nat, p:nat)
  requires fim <= palavra.Length
  requires ini+p <= fim
  modifies palavra
  ensures palavra[..ini] == old(palavra[..ini])
  ensures palavra[ini..fim-p] == old(palavra[ini+p..fim])
{
    forall i | 0 <= i < fim-(ini+p)
    { 
        palavra[ini+i] := palavra[ini+p+i];
    }
}