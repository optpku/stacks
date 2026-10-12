/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Regularity.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications

/-!
# Regular immersions into locally Noetherian schemes

For immersions into a locally Noetherian scheme, regular, Koszul-regular,
`H₁`-regular, and quasi-regular immersions are equivalent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace IsQuasiRegularImmersion

/-- A quasi-regular immersion into a locally Noetherian scheme is regular. -/
theorem isRegular_of_isLocallyNoetherian
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiRegularImmersion i] :
    IsRegularImmersion i := sorry

end IsQuasiRegularImmersion

/-- For an immersion into a locally Noetherian scheme, regular, Koszul-regular,
`H₁`-regular, and quasi-regular are equivalent. -/
theorem immersionRegularity_tfae
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] [IsLocallyNoetherian X] :
    List.TFAE
      [ IsRegularImmersion i
      , IsKoszulRegularImmersion i
      , IsH1RegularImmersion i
      , IsQuasiRegularImmersion i
      ] := sorry

end AlgebraicGeometry
