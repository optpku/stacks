/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Between.Restriction
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Coskeletal
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018A

# Coskeletons between truncation levels

For `n ≤ m`, further truncation from `m` to `n` has right adjoint
`Truncated.cosk n ⋙ truncation m`. The construction is compared with the generic right Kan
extension along `Δ≤n ⥤ Δ≤m`, and the comparison data is exposed independently of the adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace trunc

namespace cosk

/-- The right Kan extension functor from `n`-truncated to `m`-truncated simplicial objects, for
`n ≤ m`. This is the canonical extension functor for the truncation tower. -/
@[stacks 018A "right Kan extension between truncation levels"]
noncomputable abbrev functor (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n m h] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C m :=
  (SimplexCategory.Truncated.incl n m h).op.ran

/-- The universal adjunction for right Kan extension along a truncation inclusion. -/
@[stacks 018A "truncation-level right Kan extension adjunction"]
noncomputable abbrev adj (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n m h] :
    Truncated.trunc C m n h ⊣ functor n m h :=
  (SimplexCategory.Truncated.incl n m h).op.ranAdjunction C

/-- The Hom-equivalence induced by the right Kan extension adjunction between truncation levels. -/
@[stacks 018A "truncation-level right Kan extension Hom equivalence"]
noncomputable def homEquiv (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n m h]
    (U : SimplicialObject.Truncated C n) (V : SimplicialObject.Truncated C m) :
    ((Truncated.trunc C m n h).obj V ⟶ U) ≃ (V ⟶ (functor n m h).obj U) :=
  (adj n m h).homEquiv V U

/-- The forward truncation-level Hom-equivalence is the adjunction unit followed by the right
Kan extension of the given morphism. -/
@[simp, stacks 018A "forward truncation-level right Kan extension Hom equivalence"]
theorem homEquiv_apply (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n m h]
    (U : SimplicialObject.Truncated C n) (V : SimplicialObject.Truncated C m)
    (f : (Truncated.trunc C m n h).obj V ⟶ U) :
    homEquiv n m h U V f =
      (adj n m h).unit.app V ≫ (functor n m h).map f := sorry

/-- The inverse truncation-level Hom-equivalence applies further truncation and then composes
with the adjunction counit. -/
@[simp, stacks 018A "inverse truncation-level right Kan extension Hom equivalence"]
theorem homEquiv_symm_apply (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n m h]
    (U : SimplicialObject.Truncated C n) (V : SimplicialObject.Truncated C m)
    (g : V ⟶ (functor n m h).obj U) :
    (homEquiv n m h U V).symm g =
      (Truncated.trunc C m n h).map g ≫ (adj n m h).counit.app U := sorry

/-- Composing right Kan extension from level `n` to level `m` with the `m`-coskeleton gives the
`n`-coskeleton. -/
@[stacks 018B "composition of truncated right Kan extension and coskeleton"]
noncomputable def ranCompIso (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    [SimplicialObject.Truncated.Between.HasCoskeletons C n m h] :
    (functor (C := C) n m h ⋙
      Truncated.cosk (C := C) m) ≅
    Truncated.cosk (C := C) n :=
  Adjunction.rightAdjointUniq
    (((coskAdj (C := C) m).comp (adj (C := C) n m h)).ofNatIsoLeft
        (truncationCompTrunc (C := C) h))
    (coskAdj (C := C) n)

end cosk

end trunc

namespace coskeleton

namespace ofLE

/-- The universal map from a chosen `n`-coskeleton to the chosen coskeleton of its
`m`-truncation. This objectwise construction requires chosen coskeletons only for the two
truncated objects that occur in the statement. -/
@[stacks 018B "objectwise higher-coskeleton comparison"]
noncomputable def hom {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasCoskeleton]
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    U.coskeleton ⟶ ((truncation m).obj U.coskeleton).coskeleton :=
  CategoryTheory.SimplicialObject.Truncated.coskeleton.lift
    ((truncation m).obj U.coskeleton) U.coskeleton (𝟙 _)

/-- Restricting the objectwise higher-coskeleton comparison and composing with the chosen counit
recovers the identity of the `m`-truncation. -/
@[reassoc (attr := simp), stacks 018B "objectwise higher-coskeleton comparison on the counit"]
theorem hom_counit {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasCoskeleton]
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    (SimplexCategory.Truncated.inclusion m).op.whiskerLeft (hom (m := m) U) ≫
        coskeleton.counit ((truncation m).obj U.coskeleton) =
      𝟙 ((truncation m).obj U.coskeleton) := sorry

/-- The objectwise higher-coskeleton comparison is invertible when its source coskeleton level is
at most its target level. -/
@[stacks 018B "invertibility of the objectwise higher-coskeleton comparison"]
theorem hom.isIso_of_le {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    IsIso (hom (m := m) U) := sorry

/-- The explicit inverse obtained by restricting the higher coskeleton counit to level `n` and
lifting along the chosen `n`-coskeleton. -/
@[stacks 018B "explicit inverse of the objectwise higher-coskeleton comparison"]
noncomputable def inv {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    ((truncation m).obj U.coskeleton).coskeleton ⟶ U.coskeleton :=
  CategoryTheory.SimplicialObject.Truncated.coskeleton.lift U
    ((truncation m).obj U.coskeleton).coskeleton
    (((SimplexCategory.Truncated.incl n m h).op.whiskerLeft
      (CategoryTheory.SimplicialObject.Truncated.coskeleton.counit
        ((truncation m).obj U.coskeleton))) ≫
      Between.coskeleton.restriction.counit U m h)

/-- The objectwise higher-coskeleton comparison followed by its inverse is the identity. -/
@[simp, stacks 018B "objectwise higher-coskeleton forward-inverse law"]
theorem hom_inv_id {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    hom (m := m) U ≫ inv U h = 𝟙 U.coskeleton := sorry

/-- The objectwise higher-coskeleton inverse followed by the comparison is the identity. -/
@[simp, stacks 018B "objectwise higher-coskeleton inverse-forward law"]
theorem inv_hom_id {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    inv U h ≫ hom (m := m) U =
      𝟙 ((truncation m).obj U.coskeleton).coskeleton := sorry

/-- A chosen pointwise `n`-coskeleton is canonically isomorphic to the chosen coskeleton of its
`m`-truncation for every `n ≤ m`. -/
@[stacks 018B "objectwise higher-coskeleton isomorphism"]
noncomputable def iso {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    U.coskeleton ≅ ((truncation m).obj U.coskeleton).coskeleton :=
  { hom := hom (m := m) U
    inv := inv U h
    hom_inv_id := hom_inv_id U h
    inv_hom_id := inv_hom_id U h }

/-- The forward map of the objectwise higher-coskeleton isomorphism is its universal lift. -/
@[simp, stacks 018B "objectwise higher-coskeleton isomorphism forward map"]
theorem iso_hom {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    (iso U h).hom = hom (m := m) U := sorry

/-- The inverse map of the objectwise higher-coskeleton isomorphism is the named inverse. -/
@[simp, stacks 018B "objectwise higher-coskeleton isomorphism inverse map"]
theorem iso_inv {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m)
    [((truncation m).obj U.coskeleton).HasCoskeleton] :
    (iso U h).inv = inv U h := sorry

end ofLE

end coskeleton

namespace cosk

namespace ofLE

/-- The higher-coskeleton unit, regarded as an isomorphism on an `n`-coskeleton. -/
@[stacks 018B "higher-coskeleton unit isomorphism"]
noncomputable def iso (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (Truncated.cosk n).obj U ≅
      (Truncated.cosk m).obj ((truncation m).obj ((Truncated.cosk n).obj U)) :=
  coskeleton.ofLE.iso U h

/-- The uniform higher-coskeleton isomorphism is the objectwise chosen-coskeleton comparison. -/
@[simp, stacks 018B "uniform and objectwise higher-coskeleton comparison"]
theorem iso_eq_objectwise (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    iso n m h U = coskeleton.ofLE.iso U h := sorry

/-- The canonical inverse to the higher-coskeleton unit on an `n`-coskeleton. -/
@[stacks 018B "inverse to the higher-coskeleton unit"]
noncomputable def inv (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (Truncated.cosk m).obj ((truncation m).obj ((Truncated.cosk n).obj U)) ⟶
      (Truncated.cosk n).obj U :=
  coskeleton.ofLE.inv U h

/-- The higher-coskeleton unit followed by `cosk.ofLE.inv` is the identity. -/
@[stacks 018B "higher-coskeleton unit inverse law"]
theorem hom_inv_id (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (coskAdj m).unit.app ((Truncated.cosk n).obj U) ≫ inv n m h U =
      𝟙 ((Truncated.cosk n).obj U) := sorry

/-- `cosk.ofLE.inv` followed by the higher-coskeleton unit is the identity. -/
@[stacks 018B "higher-coskeleton inverse unit law"]
theorem inv_hom_id (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    inv n m h U ≫ (coskAdj m).unit.app ((Truncated.cosk n).obj U) =
      𝟙 ((Truncated.cosk m).obj ((truncation m).obj ((Truncated.cosk n).obj U))) := sorry

/-- The forward map of `cosk.ofLE.iso` is the unit of the higher coskeleton adjunction. -/
@[simp, stacks 018B "higher-coskeleton comparison forward map"]
theorem iso_hom (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (iso n m h U).hom =
      (coskAdj m).unit.app ((Truncated.cosk n).obj U) := sorry

/-- The inverse map of `cosk.ofLE.iso` is the named inverse to the higher-coskeleton unit. -/
@[simp, stacks 018B "higher-coskeleton comparison inverse map"]
theorem iso_inv (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (iso n m h U).inv = inv n m h U := sorry

/-- The component isomorphisms `cosk.ofLE.iso` are natural in the truncated simplicial object. -/
@[stacks 018B "higher-coskeleton comparison naturality"]
theorem naturality (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    {U V : SimplicialObject.Truncated C n} (f : U ⟶ V) :
    (Truncated.cosk n).map f ≫ (iso n m h V).hom =
      (iso n m h U).hom ≫
        (((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
          truncation m) ⋙ Truncated.cosk m).map f := sorry

/-- The unit comparison is natural: an `n`-coskeleton is canonically isomorphic to its
`m`-coskeleton for every `n ≤ m`. -/
@[stacks 018B "coskeleton comparison across truncation levels"]
noncomputable def natIso (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m] :
    (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ≅
      ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
        truncation m) ⋙ Truncated.cosk m :=
  NatIso.ofComponents (fun U ↦ iso n m h U)
    (fun f ↦ naturality n m h f)

/-- The component of the uniform higher-coskeleton comparison is its objectwise isomorphism. -/
@[simp, stacks 018B "higher-coskeleton natural isomorphism component"]
theorem natIso_app (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (natIso n m h).app U = iso n m h U := sorry

/-- Taking the `m`-coskeleton of the `m`-truncation of an
`n`-coskeleton recovers the original `n`-coskeleton. -/
@[stacks 018B "iterated coskeleton comparison"]
noncomputable def compIso (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m] :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
      truncation m) ⋙ Truncated.cosk m ≅
    Truncated.cosk n :=
  (natIso n m h).symm

/-- The component of the iterated-coskeleton comparison is the inverse objectwise
isomorphism. -/
@[simp, stacks 018B "iterated coskeleton natural isomorphism component"]
theorem compIso_app (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) :
    (compIso n m h).app U = (iso n m h U).symm := sorry

end ofLE

end cosk

namespace trunc

namespace cosk

namespace ranIso

/-- The objectwise comparison between the intermediate right Kan extension and the restricted
full coskeleton is natural in the truncated simplicial object. -/
@[stacks 018A "naturality of the intermediate coskeleton comparison"]
theorem naturality (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    {U V : SimplicialObject.Truncated C n} (f : U ⟶ V) :
    (functor n m h).map f ≫
        (Between.coskeleton.restriction.iso V m h).hom =
      (Between.coskeleton.restriction.iso U m h).hom ≫
        (((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
          truncation m).map f) := sorry

end ranIso

/-- The generic right Kan extension between truncation levels agrees with
truncating the ambient `n`-coskeleton. -/
@[stacks 018A "right Kan extension description of successive coskeleton stages"]
noncomputable def ranIso (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n] :
    functor n m h ≅
      (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
        truncation m :=
  NatIso.ofComponents
    (fun U ↦ Between.coskeleton.restriction.iso U m h)
    (fun f ↦ ranIso.naturality n m h f)

/-- The component of the intermediate right-Kan-extension comparison is the objectwise
restriction isomorphism. -/
@[simp, stacks 018A "intermediate coskeleton natural isomorphism component"]
theorem ranIso_app (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]
    (U : SimplicialObject.Truncated C n) :
    (ranIso n m h).app U = Between.coskeleton.restriction.iso U m h := sorry

/-- Further truncation has right adjoint given by truncating the
ambient `n`-coskeleton. -/
@[stacks 018B "coskeleton adjunction between truncation levels"]
noncomputable def adjunction (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n] :
    Truncated.trunc C m n h ⊣
      (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
        truncation m :=
  (adj (C := C) n m h).ofNatIsoRight
    (ranIso (C := C) n m h)

end cosk

end trunc

end CategoryTheory.SimplicialObject.Truncated
