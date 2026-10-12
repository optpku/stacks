/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Absolute Noetherian approximation compatible with a compact open

This file packages absolute finite-type approximations of a scheme that extend a prescribed
inverse-system presentation of a compact open subscheme.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- An absolute finite-type approximation of a scheme whose compact open subscheme is identified
with a prescribed inverse limit. -/
structure CompactOpenAbsoluteNoetherianApproximation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (V : S.Opens)
    (D : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (cV : Cone (D ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (eV : V.toScheme ≅ cV.pt) where
  /-- The directed index type of the approximating inverse system. -/
  J : Type u
  /-- The preorder on the index type of the approximating inverse system. -/
  [preorderJ : Preorder J]
  /-- The approximating inverse system has at least one stage. -/
  [nonemptyJ : Nonempty J]
  /-- Any two stages of the approximating inverse system admit a common later stage. -/
  [directedJ : IsDirected J (· ≤ ·)]
  /-- The inverse system of absolute finite-type approximating schemes. -/
  E : OrderDual J ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ)))
  /-- The cone from the original scheme to the approximating inverse system. -/
  cS : Cone (E ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ))))
  /-- The identification of the original scheme with the vertex of the approximation cone. -/
  eS : S ≅ cS.pt
  /-- The approximation cone is a limit cone. -/
  isLimitS : IsLimit cS
  /-- The order-preserving comparison from approximation stages to prescribed open stages. -/
  indexMap : J → I
  /-- The comparison of stage indices is monotone. -/
  monotoneIndexMap : Monotone indexMap
  /-- Every transition morphism in the approximating inverse system is affine. -/
  transitionAffine :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'), IsAffineHom (E.map (homOfLE hjj')).left
  /-- Every approximating stage is of finite type over `Spec ℤ`. -/
  stageFinite : ∀ j : J, Scheme.Hom.FiniteType (E.obj j).hom
  /-- The open subscheme at each approximation stage. -/
  V' : ∀ j : J, ((E.obj j).left).Opens
  /-- Each approximation-stage open is identified with the corresponding prescribed stage. -/
  stageIso : ∀ j : J, (V' j).toScheme ≅ (D.obj (indexMap j)).left
  /-- The morphism from the original compact open to each approximation-stage open. -/
  toV' : ∀ j : J, V.toScheme ⟶ (V' j).toScheme
  /-- The transition morphism between compatible approximation-stage opens. -/
  Vtransition : ∀ {j j' : J}, (hjj' : j ≤ j') → (V' j').toScheme ⟶ (V' j).toScheme
  /-- Each stage open is the limit of its inverse images along the corresponding tail. -/
  openLimit :
    ∀ j : J,
      IsLimit (opensCone (E ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))) cS j (V' j))
  /-- The inverse image in the original scheme of every approximation-stage open is `V`. -/
  openPullback :
    ∀ j : J, (Opens.map ((eS.hom ≫ cS.π.app j).base)).obj (V' j) = V
  /-- Transition morphisms pull back each stage open to the corresponding later stage open. -/
  transitionPullback :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'),
      (Opens.map ((E.map (homOfLE hjj')).left).base).obj (V' j) = V' j'
  /-- The maps from `V` to the stage opens commute with their inclusions into the stages. -/
  toOpen :
    ∀ j : J, toV' j ≫ (V' j).ι = V.ι ≫ eS.hom ≫ cS.π.app j
  /-- The maps from `V` agree with the prescribed limit projections through the stage
  identifications. -/
  toStage :
    ∀ j : J, toV' j ≫ (stageIso j).hom = eV.hom ≫ cV.π.app (indexMap j)
  /-- The transition maps between stage opens commute with their inclusions into the stages. -/
  transitionOpen :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'),
      Vtransition hjj' ≫ (V' j).ι = (V' j').ι ≫ (E.map (homOfLE hjj')).left
  /-- The transition maps between stage opens agree, through the stage identifications, with the
  transitions in the prescribed inverse system. -/
  transitionStage :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'),
      Vtransition hjj' ≫ (stageIso j).hom =
        (stageIso j').hom ≫ (D.map (homOfLE (monotoneIndexMap hjj'))).left

namespace CompactOpenAbsoluteNoetherianApproximation

/-- The scheme underlying the open subscheme at an approximation stage. -/
def openStage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {V : S.Opens}
    {D : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    {cV : Cone (D ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ))))}
    {eV : V.toScheme ≅ cV.pt}
    (A : CompactOpenAbsoluteNoetherianApproximation S V D cV eV) (j : A.J) : Scheme.{u} :=
  (A.V' j).toScheme

end CompactOpenAbsoluteNoetherianApproximation

/-- A quasi-compact quasi-separated scheme containing a compact open presented as an inverse
limit of schemes of finite type over `ℤ` admits a compatible absolute finite-type approximation. -/
theorem exists_absoluteNoetherianApproximation_of_compactOpen_inverseLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (V : S.Opens) (hV : IsCompact (V : Set S))
    (D : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (cV : Cone (D ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (hcV : IsLimit cV)
    (eV : V.toScheme ≅ cV.pt)
    (hDaffine :
      ∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left)
    (hDfinite : ∀ i : I, Scheme.Hom.FiniteType (D.obj i).hom) :
    Nonempty (CompactOpenAbsoluteNoetherianApproximation S V D cV eV) := sorry

/-- Every quasi-compact quasi-separated scheme is an inverse limit of schemes of finite type
over `ℤ` with affine transition morphisms. -/
theorem exists_absoluteNoetherianApproximation
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (cS : Cone (D ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
      (hcS : IsLimit cS) (eS : S ≅ cS.pt)
      (h_affine : ∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left),
        ∀ i : I, Scheme.Hom.FiniteType (D.obj i).hom := sorry

end AlgebraicGeometry
