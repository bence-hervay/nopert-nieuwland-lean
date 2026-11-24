import Polyhedra.Archimedean.Rhombicuboctahedron.Result
import Polyhedra.Archimedean.Rhombicuboctahedron.Proof.NuPolynomial

set_option linter.style.longLine false

/-!
# The rhombicuboctahedron: a polynomial of its Nieuwland number

`nu_polynomial`: `ν` is a root of this polynomial with integer coefficients, of degree 52
(coefficients from the constant one). The proof (`Proof/NuPolynomial.lean`) writes the root of one
of the systems of `ν` out exactly over a number field and checks it; that system has exactly one root,
at `ν`. The polynomial is irreducible over `ℚ` (checked with PARI/GP, not proved here), so that,
divided by its leading coefficient, it is the minimal polynomial of `ν`.
-/

namespace Nieuwland.Archimedean.Rhombicuboctahedron

open scoped Nieuwland.Notation

/-- **A polynomial of the Nieuwland number**: `ν` is a root of this polynomial with integer
coefficients, from the constant coefficient. -/
theorem nu_polynomial :
    polyEval [5774276, 0, -265553552, 0, 4645736104, 0, -43368609728, 0, 250413837464, 0, -962554231504, 0, 2520992948408, 0, -4313542079848, 0, 3689539225557, 0, 2656149026700, 0, -13595105430302, 0, 20175506243564, 0, -11787182530651, 0, -11484414734168, 0, 35672760795188, 0, -45444019705200, 0, 38068055383196, 0, -22911122853856, 0, 10138159931536, 0, -3293684717888, 0, 773681843600, 0, -128048895872, 0, 14397766016, 0, -1042884608, 0, 44682240, 0, -974848, 0, 8192] (ν polyhedron) = 0 :=
  Proof.nu_polynomial

end Nieuwland.Archimedean.Rhombicuboctahedron
