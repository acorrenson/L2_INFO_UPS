#include <exponentiation.h>
#include <assert.h>


/**
 * @brief      Exponentiation rapide itérative d'un "réél".
 *
 * @param[in]  a     Le réél.
 * @param[in]  b     La puissance entière.
 *
 * @return     Le réél a élevé à la puisance b.
 */
double expo_rapide(double a, int b)
{
  // precondition : b > 0
  assert(b > 0);

  double  r = 1;
  double  x = a;
  int     p = b;

  while (p > 0) {
    // invariant : rx^p = a^b
    if (p%2) {
      r = r*x;
    }
    x = x*x;
    p = p/2;
  }

  // postcondition : r = a^b
  return r;
}


/**
 * @brief      Exponentiation rapide recursive d'un réél (fonction intermédiaire).
 *
 * @param[in]  r     Le réél
 * @param[in]  x     Un accumulateur
 * @param[in]  p     La puissance entière
 *
 * @return     Le réél élevé à la puissance p.
 */
double _expo_rapide_rec(double r, double x, int p)
{
  // cas d'arrêt
  if (p == 0) {
    return r;
  }
  
  // cas puissance impaire
  if (p%2) {
    return _expo_rapide_rec(r*x, x*x, p/2);
  }

  // cas puissance paire
  return _expo_rapide_rec(r, x*x, p/2);
}


/**
 * @brief      Exponentiation rapide récursive d'un "réél".
 *
 * @param[in]  a     Le réél.
 * @param[in]  b     La puissance entière.
 *
 * @return     Le réél a élevé à la puisance b.
 */
double expo_rapide_rec(double a, int b)
{
  // precondition : b > 0
  assert(b > 0);
  
  int r = _expo_rapide_rec(1, a, b);
  
  // postcondition : r = a^b
  return r;
}


/**
 * /!\ Remarque :
 * 
 * La plupart des compilateurs C vont dérécursiver la fonction _expo_rapide_rec.
 * En fait, l'implémentation récursive (terminale) est directement équivalente à
 * l'implémentation itérative. En revanche, il est intéressant de voir comment 
 * le passage de récursif terminal à itératif est naturel.
 */
