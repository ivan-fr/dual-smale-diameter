# A critical chord bound for the dual Smale mean value problem

For a normalized complex polynomial of degree $n$ with critical points
$z_1,\ldots,z_{n-1}$ counted with multiplicity, put
$R=\max_k |z_k|$, $A=\prod_k |z_k|$, and
$M=\max_k |P(z_k)/z_k|$. For any two distinct critical points at
distance $d$, the following bound holds:

$$
M \ge \frac{2d^n}{4^n n A R}.
$$

In particular $2d^n\ge 4^n A R$ implies the conjectured $M\ge 1/n$.
One can take the longest critical chord and combine the result with the
radius bound in [dual-smale-global](https://github.com/ivan-fr/dual-smale-global/tree/8765ad9cf76ab041f49c287889096568f51df5d9).
Relative to its geometric-mean estimate, the chord estimate multiplies the
lower bound by $(d/R)^n$. The combined estimate uses $\max(d,R)$.
This is a sufficient condition for the dual Smale inequality. The case of
arbitrary critical configurations remains open in this work.

## Proof

Let $L$ exceed the largest critical-value modulus. The upstream sublevel
path theorem joins the origin to each endpoint of the chord in
$\{|P|<L\}$. Traversing one path backwards and the other forwards gives
a continuous path joining the endpoints. Distance from the first endpoint
therefore takes every value in $[0,d]$. Pick points on that path at the
scaled Chebyshev node distances. The reverse triangle inequality gives
the node separation required by the upstream monic Chebyshev theorem.
Applying it to $P/\operatorname{lc}(P)$ yields
$2d^n/4^n\le L/|\operatorname{lc}(P)|$.
Let $L$ decrease to the largest critical-value modulus. Since
$|\operatorname{lc}(P)|=1/(nA)$ and each critical modulus is at most
$R$, the stated bound follows.

## Degree ten and the remaining gap

Take critical points $1,-1, i/3$ (six copies of $i/3$), and $-i/3$.
The normalized polynomial is determined by $P(0)=0$ and
$P'(z)=\prod_k(1-z/z_k)$. Then $R=1$, $d=2$, $A=3^{-7}$.
The chord estimate gives $M\ge2187/5120>1/10$.
The upstream radius estimate gives $2187/5242880<1/10$.

For degree ten with all moduli in $[1,11/10]$, the chord estimate
itself is at most $2(11/10)^9/(2^{10}\cdot 10)<1/10$:
use $d\le2R$ and $A\ge1$. Thus comparable but unequal critical
moduli remain a genuine obstruction to proving the conjecture by this
estimate alone. This observation concerns the estimate, not the actual
maximum $M$.

## Verification

The GitHub Actions workflow checks the Lean statements in `Diameter.lean`
against a pinned revision of `dual-smale-global` and runs an exact rational
degree-ten calculation. The dependency supplies the polynomial sublevel
path theorem, the monic Chebyshev interpolation bound, and the
leading-coefficient formula.

For a local run with Elan installed:

```sh
git clone https://github.com/ivan-fr/dual-smale-global.git upstream
git -C upstream checkout 8765ad9cf76ab041f49c287889096568f51df5d9
bash verify.sh upstream/lean
```
