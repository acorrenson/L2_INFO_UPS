#include <stdio.h>
#include <stdlib.h>


/**
 * @brief      Retourne A^(A^(A^....)) | B fois.
 *
 * @param[in]  a     la base
 * @param[in]  b     le nombre d'occurences de la base dans la chaine d'exposants
 *
 */
long int puissance_puissance(long int a, long int b) {
  // Initialisation de l'exponentiation rapide iterative
  long int r = 1;
  long int x = a;
  long int p = 1;
  // Resultat temporaire
  long int temp = 1;
  // Compteur
  int c = b;
  
  while (c > 0) {
    // Exponentiation rapide
    if (p > 0) {
      if (p%2 == 1) {
        r = r * x;
      }
      x = x * x;
      p = p / 2;
    } else {
    // Réinitialisation de l'expo rapide
      temp = r;
      r = 1;
      x = a;
      p = temp;
      c = c-1;
    }
  }
  return p;
}


int main(int argc, char const *argv[])
{
  printf("%ld\n", puissance_puissance(3, 1));
  printf("%ld\n", puissance_puissance(3, 2));
  printf("%ld\n", puissance_puissance(3, 3));
  return 0;
}

