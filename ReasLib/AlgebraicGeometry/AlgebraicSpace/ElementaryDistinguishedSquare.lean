/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Elementary distinguished squares of algebraic spaces

A pair `(j : U ⟶ W, f : V ⟶ W)` is an elementary distinguished square when `j` is
an open immersion, `f` is étale, and the canonical morphism from the inverse image of
the reduced complement `T = W \ U` to `T` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A pair of morphisms `j : U ⟶ W` and `f : V ⟶ W` of algebraic spaces over `S` is an
elementary distinguished square when `j` is an open immersion, `f` is étale, and the
canonical morphism `f⁻¹(T) ⟶ T` is an isomorphism, where `T` is the reduced induced
closed subspace on `W \ U`. -/
class IsElementaryDistinguishedSquare {S : Scheme.{u}} {U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) : Prop where
  /-- The morphism `j` is an open immersion, corresponding to `U ⊂ W`. -/
  [isOpenImmersion : IsOpenImmersion j]
  /-- The morphism `f` is étale. -/
  [isEtale : Etale f]
  /-- The canonical comparison `f⁻¹(T) ⟶ T` is an isomorphism. -/
  isIso_preimage : IsIso (OpenSubspace.preimageTo (OpenSubspace.ofι j) f)

/-- The identity open immersion of `W` and an étale morphism `f : V ⟶ W` form an
elementary distinguished square. -/
instance instIsElementaryDistinguishedSquare_idι {S : Scheme.{u}}
    {V W : AlgebraicSpace S} (f : V ⟶ W) [Etale f] :
    IsElementaryDistinguishedSquare (𝟙 W) f :=
  sorry

namespace IsElementaryDistinguishedSquare

/-- The open subspace `U ⊂ W` determined by the open immersion of an elementary
distinguished square. -/
def toOpenSubspace {S : Scheme.{u}} {U V W : AlgebraicSpace S} (j : U ⟶ W)
    (f : V ⟶ W) [h : IsElementaryDistinguishedSquare j f] : OpenSubspace W :=
  ⟨U, j, h.isOpenImmersion⟩

/-- The inclusion of `toOpenSubspace j f` is `j`. -/
theorem toOpenSubspace_ι {S : Scheme.{u}} {U V W : AlgebraicSpace S} (j : U ⟶ W)
    (f : V ⟶ W) [IsElementaryDistinguishedSquare j f] :
    (toOpenSubspace j f).ι = j :=
  sorry

/-- The reduced complement `T = W \ U` associated to an elementary distinguished
square `(j, f)`. -/
abbrev closedComplement {S : Scheme.{u}} {U V W : AlgebraicSpace S} (j : U ⟶ W)
    (f : V ⟶ W) [IsElementaryDistinguishedSquare j f] : ClosedSubspace W :=
  OpenSubspace.reducedComplement (toOpenSubspace j f)

/-- The inverse image `f⁻¹(T)` of the reduced complement of an elementary
distinguished square `(j, f)`. -/
abbrev preimage {S : Scheme.{u}} {U V W : AlgebraicSpace S} (j : U ⟶ W) (f : V ⟶ W)
    [IsElementaryDistinguishedSquare j f] : AlgebraicSpace S :=
  OpenSubspace.preimageReducedComplement (toOpenSubspace j f) f

/-- The canonical comparison `f⁻¹(T) ⟶ T` of an elementary distinguished square. -/
abbrev preimageTo {S : Scheme.{u}} {U V W : AlgebraicSpace S} (j : U ⟶ W) (f : V ⟶ W)
    [IsElementaryDistinguishedSquare j f] :
    preimage j f ⟶ (closedComplement j f).X :=
  OpenSubspace.preimageTo (toOpenSubspace j f) f

/-- An elementary distinguished square consists of an open immersion, an étale
morphism, and an isomorphism `f⁻¹(T) ⟶ T`. -/
theorem spec {S : Scheme.{u}} {U V W : AlgebraicSpace S} (j : U ⟶ W) (f : V ⟶ W)
    [h : IsElementaryDistinguishedSquare j f] :
    IsOpenImmersion j ∧ Etale f ∧ IsIso (preimageTo j f) :=
  sorry

/-- An open subspace `U ⊂ W` and an étale morphism `f : V ⟶ W` form an elementary
distinguished square when `f⁻¹(T) ⟶ T` is an isomorphism. -/
theorem ofOpenSubspace {S : Scheme.{u}} {V W : AlgebraicSpace S} (U : OpenSubspace W)
    (f : V ⟶ W) [Etale f] (h : IsIso (OpenSubspace.preimageTo U f)) :
    IsElementaryDistinguishedSquare U.ι f :=
  sorry

end IsElementaryDistinguishedSquare

/-- For an open immersion `j`, being an elementary distinguished square is étaleness of
`f` together with the canonical comparison `f⁻¹(T) ⟶ T` being an isomorphism. -/
theorem isElementaryDistinguishedSquare_iff {S : Scheme.{u}} {U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) [IsOpenImmersion j] :
    IsElementaryDistinguishedSquare j f ↔
      Etale f ∧ IsIso (OpenSubspace.preimageTo (OpenSubspace.ofι j) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
