import Polyhedra.Archimedean.TruncatedIcosidodecahedron.Result
import Polyhedra.Archimedean.TruncatedIcosidodecahedron.Proof.NuPolynomial

set_option linter.style.longLine false

/-!
# The truncated icosidodecahedron: a polynomial of its Nieuwland number

`nu_polynomial`: `ν` is a root of this polynomial with integer coefficients, of degree 52
(coefficients from the constant one). The proof (`Proof/NuPolynomial.lean`) writes the root of one
of the systems of `ν` out exactly over a number field and checks it; that system has exactly one root,
at `ν`. The polynomial is irreducible over `ℚ` (checked with PARI/GP, not proved here), so that,
divided by its leading coefficient, it is the minimal polynomial of `ν`.
-/

namespace Nieuwland.Archimedean.TruncatedIcosidodecahedron

open scoped Nieuwland.Notation

/-- **A polynomial of the Nieuwland number**: `ν` is a root of this polynomial with integer
coefficients, from the constant coefficient. -/
theorem nu_polynomial :
    polyEval [13506860952860688433360140625, 0, -5425310826527841530875116050000, 0, 167061833787985834031920710172500, 0, -2260941268420183763711332224448000, 0, 18389865026540318827295913605153950, 0, -102849056937341216553092854611576000, 0, 425755809638229430948762155149847076, 0, -1365560910297002123623197658426085424, 0, 3498777451100651167679925110506396057, 0, -7315653246430038039318749795221452432, 0, 12675730221461401318490254415666582816, 0, -18402308783912969945389345573556030896, 0, 22560406104335597365837240112059244832, 0, -23478067910606793329927095168764957696, 0, 20802048049614319675623308432139184192, 0, -15705629720142589326450580706036835840, 0, 10091979692365778432134984654069942528, 0, -5499940451363213423686155579240112128, 0, 2526797360365756637019844586203441152, 0, -969668938506632752539870154646040576, 0, 306740276465662761836904513653243904, 0, -78496474570775237531100027360706560, 0, 15817027008888164554780841374334976, 0, -2410285848270745220139246012334080, 0, 260346432698676746233318425231360, 0, -17701133313858498522046424678400, 0, 567172013821948836610729574400] (ν polyhedron) = 0 :=
  Proof.nu_polynomial

end Nieuwland.Archimedean.TruncatedIcosidodecahedron
