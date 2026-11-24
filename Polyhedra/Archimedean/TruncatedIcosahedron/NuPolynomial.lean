import Polyhedra.Archimedean.TruncatedIcosahedron.Result
import Polyhedra.Archimedean.TruncatedIcosahedron.Proof.NuPolynomial

set_option linter.style.longLine false

/-!
# The truncated icosahedron: a polynomial of its Nieuwland number

`nu_polynomial`: `ν` is a root of this polynomial with integer coefficients, of degree 36
(coefficients from the constant one). The proof (`Proof/NuPolynomial.lean`) writes the root of one
of the systems of `ν` out exactly over a number field and checks it; that system has exactly one root,
at `ν`. The polynomial is irreducible over `ℚ` (checked with PARI/GP, not proved here), so that,
divided by its leading coefficient, it is the minimal polynomial of `ν`.
-/

namespace Nieuwland.Archimedean.TruncatedIcosahedron

open scoped Nieuwland.Notation

/-- **A polynomial of the Nieuwland number**: `ν` is a root of this polynomial with integer
coefficients, from the constant coefficient. -/
theorem nu_polynomial :
    polyEval [9909483771415953723059055022225, 0, -1100467790013946451493795575202015, 0, 33727650165032149156534094594870104, 0, -352144628944029016214736367080370827, 0, 1935994847968847665602322979652797875, 0, -6599135534124882707608000646027763296, 0, 15123040146475081007415729588083812200, 0, -24374809411858109701622528269722073899, 0, 28335432488510256142624045950079018118, 0, -24043835908729451390391051571907695272, 0, 14919531283523126683842385301199494901, 0, -6723125585503173448354854107994825513, 0, 2166977095726894524307128219678923571, 0, -487928921271825596753916111714630300, 0, 74219620600297357536227628532571010, 0, -7264326223048157871717793722489297, 0, 424522238180235311868681103691715, 0, -12927444849216006878449563710157, 0, 147218097803559259807206749961] (ν polyhedron) = 0 :=
  Proof.nu_polynomial

end Nieuwland.Archimedean.TruncatedIcosahedron
