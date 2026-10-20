module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Induction on quasi-compact quasi-separated spaces-étale objects

Properties holding on affine objects and preserved by elementary distinguished squares
hold on all quasi-compact quasi-separated objects of the spaces-étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A property of objects of `X_spaces,étale` that holds for every affine object and is
preserved by elementary distinguished squares `(j : U ⟶ W, f : V ⟶ W)` with `W`
quasi-compact and quasi-separated, `U` quasi-compact, `V` affine, and the property true
on `U`, `V`, and `U ×_W V`, holds for every quasi-compact quasi-separated object of the
site. -/
theorem qcqsSpacesEtale_induction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [h_etale : Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left] :
    P W :=
  sorry

/-- A property of a set of spaces-étale objects holds on every member if the set contains
all affine objects, is closed under quasi-compact open subobjects, and the property is
preserved by the specified elementary distinguished squares. -/
theorem qcqsSpacesEtale_induction_mem {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (B : Set (spacesEtaleSite X)) (P : spacesEtaleSite X → Prop)
    (h_isQuasiCompact : ∀ W ∈ B, IsQuasiCompact W.left)
    (h_isAbsolutelyQuasiSeparated : ∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left)
    (h_open : ∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
      [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B)
    (h_affine_mem : ∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B)
    (h_affine : ∀ (V : spacesEtaleSite X) [IsAffine V.left], P V)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      W ∈ B → P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) (hW : W ∈ B) : P W :=
  sorry

/-- A property of spaces-étale objects that holds on affine objects and is preserved
by elementary distinguished squares with quasi-compact quasi-separated target,
quasi-compact open part, and affine étale part holds on the identity object. -/
theorem qcqsSpacesEtale_induction_self {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [h_etale : Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelyQuasiSeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W) :
    P (spacesEtaleSite.self X) :=
  @qcqsSpacesEtale_induction S X inferInstance inferInstance P h_affine h_square
    (spacesEtaleSite.self X) ‹IsQuasiCompact X› ‹IsAbsolutelyQuasiSeparated X›

end AlgebraicGeometry.AlgebraicSpace
