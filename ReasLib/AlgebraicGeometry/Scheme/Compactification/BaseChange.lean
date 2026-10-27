/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Isomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

section
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S S' W T Y Y' : C} (a : S' ⟶ S) (p : W ⟶ S) (q : T ⟶ W)

variable (j : Y ⟶ W) (b : Y' ⟶ Y) (j' : Y' ⟶ pullback a p)
  (h : j' ≫ pullback.snd a p = b ≫ j)

-- Local declaration justification (module visibility): allow this private concrete pullback
-- construction in the public ambient isomorphism without adding a public helper.
set_option backward.privateInPublic true in
/-- Identify the interior of the iterated ambient with the pullback of the old interior. -/
private def interiorAmbientIso :
    pullback j' (pullback.fst (pullback.snd a p) q) ≅
      pullback b (pullback.fst j q) :=
  pullbackRightPullbackFstIso (pullback.snd a p) q j' ≪≫
    pullback.congrHom h rfl ≪≫ (pullbackRightPullbackFstIso j q b).symm

@[reassoc (attr := simp)]
private theorem interiorAmbientIso_hom_fst :
    (interiorAmbientIso a p q j b j' h).hom ≫ pullback.fst b (pullback.fst j q) =
      pullback.fst j' (pullback.fst (pullback.snd a p) q) := by
  simp [interiorAmbientIso, pullback.congrHom_hom, Category.assoc,
    pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem interiorAmbientIso_hom_snd_snd :
    (interiorAmbientIso a p q j b j' h).hom ≫
        pullback.snd b (pullback.fst j q) ≫ pullback.snd j q =
      pullback.snd j' (pullback.fst (pullback.snd a p) q) ≫
        pullback.snd (pullback.snd a p) q := by
  simp [interiorAmbientIso, pullback.congrHom_hom, Category.assoc,
    pullback.map, pullback.lift_snd]

/-- The outer first projection and the innermost second projection determine a map. -/
private theorem nestedPullback_hom_ext {V : C}
    {s t : V ⟶ pullback b (pullback.fst j q)}
    (hf : s ≫ pullback.fst b (pullback.fst j q) =
      t ≫ pullback.fst b (pullback.fst j q))
    (hs : s ≫ pullback.snd b (pullback.fst j q) ≫ pullback.snd j q =
      t ≫ pullback.snd b (pullback.fst j q) ≫ pullback.snd j q) : s = t := by
  apply (cancel_mono (pullbackRightPullbackFstIso j q b).hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackRightPullbackFstIso_hom_fst] using hf
  · simpa only [Category.assoc, pullbackRightPullbackFstIso_hom_snd] using hs

end CategoryTheory.Limits

end
end

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

variable {X Y X' Y' : Scheme.{u}}

/-- The over-object for `f` has the same underlying morphism as `f`. -/
instance instIsSeparated_overMk (f : X ⟶ Y) [IsSeparated f] :
    IsSeparated (Over.mk f).hom :=
  inferInstanceAs (IsSeparated f)

/-- Quasi-compactness of `X` transfers to the source of `Over.mk f`. -/
instance instCompactSpace_overMk_left (f : X ⟶ Y) [CompactSpace X] :
    CompactSpace (Over.mk f).left :=
  inferInstanceAs (CompactSpace X)

/-- The interior immersion of a compactification is étale. -/
instance instEtale_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    Etale (Of.ι P) :=
  inferInstance

/-- The interior immersion of a compactification is separated. -/
instance instIsSeparated_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    IsSeparated (Of.ι P) :=
  sorry

/-- The interior immersion of a compactification is locally quasi-finite. -/
instance instLocallyQuasiFinite_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    LocallyQuasiFinite (Of.ι P) :=
  sorry

/-- The interior immersion of a compactification is locally of finite type. -/
instance instLocallyOfFiniteType_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    LocallyOfFiniteType (Of.ι P) :=
  sorry

/-- Quasi-separatedness of `X` transfers to the source of `Over.mk f`. -/
instance instQuasiSeparatedSpace_overMk_left (f : X ⟶ Y)
    [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace (Over.mk f).left :=
  inferInstanceAs (QuasiSeparatedSpace X)

/-- Cartesian base change of a separated morphism is separated. -/
theorem isSeparated_f' (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) [IsSeparated f] :
    IsSeparated f' :=
  sorry

/-- Cartesian base change of a finite-type morphism is of finite type. -/
theorem finiteType_f' (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) [Scheme.Hom.FiniteType f] :
    Scheme.Hom.FiniteType f' :=
  sorry

/-- The ambient scheme `X̄'` of the base-changed compactification, the fibre
product of `g` and the structure map of `P`. -/
def ambient (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) : Scheme.{u} :=
  pullback g P.obj.right.hom

/-- The structure map `f̄' : X̄' ⟶ Y'` of the base-changed compactification. -/
def ambientToBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    ambient f g f' g' h_cart P ⟶ Y' :=
  pullback.fst g P.obj.right.hom

/-- The base change `ḡ' : X̄' ⟶ X̄` of the compactification ambient. -/
def ambientToSource (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    ambient f g f' g' h_cart P ⟶ P.obj.right.left :=
  pullback.snd g P.obj.right.hom

/-- The compactification triangle `j ≫ f̄ = f`. -/
theorem interior_triangle (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of.ι P ≫ P.obj.right.hom = f :=
  Over.w P.obj.hom

/-- The lift witness `f' ≫ g = (g' ≫ j) ≫ f̄` for the interior of the
base-changed compactification. -/
theorem interior_fac (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    (g' ≫ Of.ι P) ≫ P.obj.right.hom = f' ≫ g :=
  (Category.assoc g' (Of.ι P) P.obj.right.hom).symm.trans
    ((congrArg (fun h ↦ g' ≫ h)
        (interior_triangle f g f' g' h_cart P)).trans h_cart.w)

/-- The ambient square of the chosen compactification is the defining pullback
of `g` and `f̄`. -/
def ambient_isPullback (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsPullback (ambientToSource f g f' g' h_cart P)
      (ambientToBase f g f' g' h_cart P) P.obj.right.hom g :=
  (IsPullback.of_hasPullback g P.obj.right.hom).flip

/-- The interior immersion `j' : X' ⟶ X̄'` induced by the cartesian square and
the compactification triangle. -/
def interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    X' ⟶ ambient f g f' g' h_cart P :=
  (ambient_isPullback f g f' g' h_cart P).lift (g' ≫ Of.ι P) f'
    (interior_fac f g f' g' h_cart P)

/-- The triangle `j' ≫ f̄' = f'`. -/
theorem interiorLift_comp_toBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    interiorLift f g f' g' h_cart P ≫ ambientToBase f g f' g' h_cart P = f' :=
  IsPullback.lift_snd (ambient_isPullback f g f' g' h_cart P) (g' ≫ Of.ι P) f'
    (interior_fac f g f' g' h_cart P)

/-- The triangle `j' ≫ ḡ' = g' ≫ j`. -/
theorem interiorLift_comp_toSource (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    interiorLift f g f' g' h_cart P ≫ ambientToSource f g f' g' h_cart P =
      g' ≫ Of.ι P :=
  IsPullback.lift_fst (ambient_isPullback f g f' g' h_cart P) (g' ≫ Of.ι P) f'
    (interior_fac f g f' g' h_cart P)

/-- The interior square of the compactification cube is cartesian. -/
theorem interior_isPullback (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsPullback g' (interiorLift f g f' g' h_cart P) (Of.ι P)
      (ambientToSource f g f' g' h_cart P) :=
  IsPullback.of_bot'
    ((interior_triangle f g f' g' h_cart P).symm ▸ h_cart)
    (ambient_isPullback f g f' g' h_cart P)

/-- The induced interior `j'` is an open immersion. -/
instance instIsOpenImmersion_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    IsOpenImmersion (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is quasi-compact. -/
instance instQuasiCompact_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    QuasiCompact (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is étale. -/
instance instEtale_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Etale (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is separated. -/
instance instIsSeparated_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsSeparated (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is locally quasi-finite. -/
instance instLocallyQuasiFinite_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    LocallyQuasiFinite (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is locally of finite type. -/
instance instLocallyOfFiniteType_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    LocallyOfFiniteType (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The structure map `f̄'` is proper, as a base change of the proper ambient
map of `P`. -/
instance instIsProper_ambientToBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsProper (ambientToBase f g f' g' h_cart P) :=
  sorry

/-- The ambient of the base-changed compactification is quasi-compact. -/
instance instCompactSpace_ambient [CompactSpace Y'] (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    CompactSpace (ambient f g f' g' h_cart P) :=
  sorry

/-- The ambient of the base-changed compactification is quasi-separated. -/
instance instQuasiSeparatedSpace_ambient [QuasiSeparatedSpace Y'] (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    QuasiSeparatedSpace (ambient f g f' g' h_cart P) :=
  sorry

/-- Compactification of `f'` obtained by base-changing the interior and
ambient of `P`. -/
def compactificationPullback (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of Y' (Over.mk f') :=
  @Of.mk Y' (Over.mk f') (Over.mk (ambientToBase f g f' g' h_cart P))
    (Over.homMk (interiorLift f g f' g' h_cart P)
      (interiorLift_comp_toBase f g f' g' h_cart P))
    (instIsOpenImmersion_interiorLift f g f' g' h_cart P)
    (instQuasiCompact_interiorLift f g f' g' h_cart P)
    (instIsProper_ambientToBase f g f' g' h_cart P)

/-- The interior immersion of the base-changed compactification is `j'`. -/
theorem compactificationPullback_ι (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of.ι (compactificationPullback f g f' g' h_cart P) =
      interiorLift f g f' g' h_cart P :=
  rfl

/-- The structure map of the base-changed compactification is `f̄'`. -/
theorem compactificationPullback_hom (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    (compactificationPullback f g f' g' h_cart P).obj.right.hom =
      ambientToBase f g f' g' h_cart P :=
  rfl

/-- Interior, ambient, and cartesian identifications of the base-changed
compactification. -/
theorem compactificationPullback_spec (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of.ι (compactificationPullback f g f' g' h_cart P) =
        interiorLift f g f' g' h_cart P ∧
      (compactificationPullback f g f' g' h_cart P).obj.right.hom =
        ambientToBase f g f' g' h_cart P ∧
      IsPullback (ambientToSource f g f' g' h_cart P)
          (ambientToBase f g f' g' h_cart P) P.obj.right.hom g ∧
      IsPullback g' (interiorLift f g f' g' h_cart P) (Of.ι P)
        (ambientToSource f g f' g' h_cart P) :=
  sorry

/-- The commutativity witness for the induced map of pulled-back ambients. -/
theorem ambientMapLift_fac (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    ambientToBase f g f' g' h_cart P ≫ g =
      (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ) ≫
        Q.obj.right.hom :=
  ((pullback.condition :
        ambientToBase f g f' g' h_cart P ≫ g =
          ambientToSource f g f' g' h_cart P ≫ P.obj.right.hom).trans
    ((congrArg (fun h ↦ ambientToSource f g f' g' h_cart P ≫ h)
        (Of.ambientMap_comp_structure φ).symm).trans
      (Category.assoc (ambientToSource f g f' g' h_cart P) (Of.ambientMap φ)
        Q.obj.right.hom).symm))

/-- The scheme map of ambients `X̄'_P ⟶ X̄'_Q` induced by a morphism of
compactifications. -/
def ambientMapLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)} (φ : P ⟶ Q) :
    ambient f g f' g' h_cart P ⟶ ambient f g f' g' h_cart Q :=
  pullback.lift (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ)
    (ambientMapLift_fac f g f' g' h_cart φ)

/-- The induced ambient map lies over `Y'`. -/
theorem ambientMapLift_comp_toBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    ambientMapLift f g f' g' h_cart φ ≫ ambientToBase f g f' g' h_cart Q =
      ambientToBase f g f' g' h_cart P :=
  pullback.lift_fst (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ)
    (ambientMapLift_fac f g f' g' h_cart φ)

/-- The induced ambient map lies over the original ambient map of `φ`. -/
theorem ambientMapLift_comp_toSource (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    ambientMapLift f g f' g' h_cart φ ≫ ambientToSource f g f' g' h_cart Q =
      ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ :=
  pullback.lift_snd (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ)
    (ambientMapLift_fac f g f' g' h_cart φ)

/-- The induced interiors commute with `ambientMapLift`. -/
theorem interiorLift_comp_ambientMapLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    {P Q : Of Y (Over.mk f)} (φ : P ⟶ Q) :
    interiorLift f g f' g' h_cart P ≫ ambientMapLift f g f' g' h_cart φ =
      interiorLift f g f' g' h_cart Q :=
  sorry

/-- The ambient scheme of the constructed compactification is the fibre
product `ambient`. -/
theorem compactificationPullback_obj_right_left (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    (compactificationPullback f g f' g' h_cart P).obj.right.left =
      ambient f g f' g' h_cart P :=
  rfl


/-- Base change sends a compactification morphism to its induced ambient lift. -/
def compactificationPullbackHom (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    compactificationPullback f g f' g' h_cart P ⟶
      compactificationPullback f g f' g' h_cart Q :=
  ObjectProperty.homMk (Under.homMk
    (Over.homMk (ambientMapLift f g f' g' h_cart φ)
      (ambientMapLift_comp_toBase f g f' g' h_cart φ)) (by
        ext
        exact interiorLift_comp_ambientMapLift f g f' g' h_cart φ))

/-- The ambient map of the base-changed morphism is its pullback lift. -/
theorem compactificationPullbackHom_ambientMap (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    {P Q : Of Y (Over.mk f)} (φ : P ⟶ Q) :
    Of.ambientMap (compactificationPullbackHom f g f' g' h_cart φ) =
      ambientMapLift f g f' g' h_cart φ := rfl


variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
variable {X' Y' Z' : Scheme.{u}}

/-- The ambient square of the pulled-back `P_bar` is cartesian. -/
theorem CompDiagram.pullback_P_bar_isPullback
    [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    [IsSeparated g] [Scheme.Hom.FiniteType g]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (C : CompDiagram X g) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z)
    (b : Y' ⟶ Y) (c : X' ⟶ X.left) (h_upper : IsPullback c f' X.hom b)
    (h_lower : IsPullback b g' g a) :
    IsPullback c
      (f' ≫ Of.ι (compactificationPullback g a g' b h_lower C.P_g))
      (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g) :=
  sorry

/-- Compactification diagram of `f'` and `g'` obtained by base change of `C`. -/
def CompDiagram.pullback
    [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    [IsSeparated g] [Scheme.Hom.FiniteType g]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (C : CompDiagram X g) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z)
    (b : Y' ⟶ Y) (c : X' ⟶ X.left) (h_upper : IsPullback c f' X.hom b)
    (h_lower : IsPullback b g' g a)
    [IsSeparated f'] [Scheme.Hom.FiniteType f']
    [IsSeparated g'] [Scheme.Hom.FiniteType g']
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Z'] [QuasiSeparatedSpace Z'] :
    CompDiagram (Over.mk f') g' :=
  let P_g' := compactificationPullback g a g' b h_lower C.P_g
  CompDiagram.of (Over.mk f') g' P_g'
    (compactificationPullback (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι P_g') c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower)
      C.P_bar)

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale
end

noncomputable section
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g) {X' Y' Z' : Scheme.{u}}
  (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X.left)
  (h_upper : IsPullback c f' X.hom b) (h_lower : IsPullback b g' g a)
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [IsSeparated g'] [Scheme.Hom.FiniteType g']
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Z'] [QuasiSeparatedSpace Z']

/-- The interior compactification written over the morphism `X.hom`. -/
def ofInteriorHom : Of Y (Over.mk X.hom) :=
  @Of.mk Y (Over.mk X.hom) (Over.mk (CompDiagram.toBase X g C))
    (Over.homMk (CompDiagram.ιInterior X g C) (CompDiagram.ιInterior_comp_toBase X g C))
    (CompDiagram.isOpenImmersion_ιInterior X g C)
    (CompDiagram.quasiCompact_ιInterior X g C)
    (CompDiagram.isProper_toBase X g C)

/-- The fixed-interior view preserves the interior immersion of the composition diagram. -/
theorem ofInteriorHom_ι : Of.ι (ofInteriorHom X g C) = CompDiagram.ιInterior X g C := rfl
/-- The fixed-interior view preserves the structure morphism of the composition diagram. -/
theorem ofInteriorHom_hom :
    (ofInteriorHom X g C).obj.right.hom = CompDiagram.toBase X g C := rfl

/-- The iterated ambient of the pulled-back composite identifies with the direct pullback. -/
def compositeCompactificationAmbientIso :
    (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left ≅
    (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).obj.right.left :=
  pullbackLeftPullbackSndIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom

/-- The ambient comparison is over the new base. -/
theorem compositeCompactificationAmbientIso_over :
    (compositeCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom ≫
        (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
          (CompDiagram.ofComposite X g C)).obj.right.hom =
      (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
        (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom :=
  pullbackLeftPullbackSndIso_hom_fst a C.P_g.obj.right.hom C.P_bar.obj.right.hom

/-- The ambient comparison preserves the fixed interior. -/
theorem compositeCompactificationAmbientIso_interior :
    Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) ≫
        (compositeCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom =
      Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)) := by
  let D := CompDiagram.pullback X g C f' g' a b c h_upper h_lower
  let Q := compactificationPullback (X.hom ≫ g) a (f' ≫ g') c
    (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  have hI_base : Of.ι D.P_bar ≫
      pullback.fst (pullback.snd a C.P_g.obj.right.hom) C.P_bar.obj.right.hom =
      f' ≫ interiorLift g a g' b h_lower C.P_g :=
    interiorLift_comp_toBase (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι (compactificationPullback g a g' b h_lower C.P_g)) c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower) C.P_bar
  have hI_source : Of.ι D.P_bar ≫
      pullback.snd (pullback.snd a C.P_g.obj.right.hom) C.P_bar.obj.right.hom =
      c ≫ Of.ι C.P_bar :=
    interiorLift_comp_toSource (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι (compactificationPullback g a g' b h_lower C.P_g)) c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower) C.P_bar
  have hQ_base : Of.ι Q ≫ pullback.fst a
      (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) = f' ≫ g' :=
    interiorLift_comp_toBase (X.hom ≫ g) a (f' ≫ g') c
      (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  have hQ_source : Of.ι Q ≫ pullback.snd a
      (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) =
      c ≫ Of.ι (CompDiagram.ofComposite X g C) :=
    interiorLift_comp_toSource (X.hom ≫ g) a (f' ≫ g') c
      (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)
  rw [CompDiagram.ofComposite_ι, CompDiagram.ιInterior_comp_openImmersion]
  change Of.ι D.P_bar ≫
    (pullbackLeftPullbackSndIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom).hom = Of.ι Q
  apply pullback.hom_ext
  · change (Of.ι D.P_bar ≫
        (pullbackLeftPullbackSndIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom).hom) ≫
        pullback.fst a (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) = _
    refine Eq.trans ?_ hQ_base.symm
    calc
      _ = Of.ι D.P_bar ≫ ((pullbackLeftPullbackSndIso a C.P_g.obj.right.hom
          C.P_bar.obj.right.hom).hom ≫ pullback.fst a
          (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom)) := Category.assoc _ _ _
      _ = Of.ι D.P_bar ≫ (pullback.fst (pullback.snd a C.P_g.obj.right.hom)
          C.P_bar.obj.right.hom ≫ pullback.fst a C.P_g.obj.right.hom) :=
        congrArg (fun k => Of.ι D.P_bar ≫ k)
          (pullbackLeftPullbackSndIso_hom_fst a C.P_g.obj.right.hom C.P_bar.obj.right.hom)
      _ = (Of.ι D.P_bar ≫ pullback.fst (pullback.snd a C.P_g.obj.right.hom)
          C.P_bar.obj.right.hom) ≫ pullback.fst a C.P_g.obj.right.hom :=
        (Category.assoc _ _ _).symm
      _ = (f' ≫ interiorLift g a g' b h_lower C.P_g) ≫
          pullback.fst a C.P_g.obj.right.hom :=
        congrArg (fun k => k ≫ pullback.fst a C.P_g.obj.right.hom) hI_base
      _ = f' ≫ g' := (Category.assoc _ _ _).trans
        (congrArg (fun k => f' ≫ k) (interiorLift_comp_toBase g a g' b h_lower C.P_g))
  · change (Of.ι D.P_bar ≫
        (pullbackLeftPullbackSndIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom).hom) ≫
        pullback.snd a (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) = _
    refine Eq.trans ?_ (hQ_source.trans
      (congrArg (fun k => c ≫ k) (CompDiagram.ιInterior_comp_openImmersion X g C))).symm
    calc
      _ = Of.ι D.P_bar ≫ ((pullbackLeftPullbackSndIso a C.P_g.obj.right.hom
          C.P_bar.obj.right.hom).hom ≫ pullback.snd a
          (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom)) := Category.assoc _ _ _
      _ = Of.ι D.P_bar ≫ pullback.snd (pullback.snd a C.P_g.obj.right.hom)
          C.P_bar.obj.right.hom := congrArg (fun k => Of.ι D.P_bar ≫ k)
        (pullbackLeftPullbackSndIso_hom_snd a C.P_g.obj.right.hom C.P_bar.obj.right.hom)
      _ = c ≫ Of.ι C.P_bar := hI_source

/-- The actual isomorphism between iterated and direct composite compactifications. -/
def compositeCompactificationIso :
    CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) ≅
    compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) :=
  Of.isoMkOfAmbient (compositeCompactificationAmbientIso X g C f' g' a b c h_upper h_lower)
    (compositeCompactificationAmbientIso_interior X g C f' g' a b c h_upper h_lower)
    (compositeCompactificationAmbientIso_over X g C f' g' a b c h_upper h_lower)

-- Local declaration justification (module visibility): expose the private pullback transport
-- only in the explicit geometric isomorphism that uses it.
set_option backward.privateInPublic true in
/-- The ambient comparison from the pulled-back diagram's interior to the direct upper pullback. -/
def interiorCompactificationAmbientIso :
    (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left ≅
    (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left :=
  CategoryTheory.Limits.interiorAmbientIso a C.P_g.obj.right.hom C.P_bar.obj.right.hom (Of.ι C.P_g) b
    (interiorLift g a g' b h_lower C.P_g)
    (interiorLift_comp_toSource g a g' b h_lower C.P_g)

/-- The interior ambient comparison preserves the projection to `Y'`. -/
theorem interiorCompactificationAmbientIso_over :
    (interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom ≫
        (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.hom =
      (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
        (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom :=
  interiorAmbientIso_hom_fst a C.P_g.obj.right.hom C.P_bar.obj.right.hom (Of.ι C.P_g) b
    (interiorLift g a g' b h_lower C.P_g)
    (interiorLift_comp_toSource g a g' b h_lower C.P_g)

/-- The interior ambient comparison preserves the actual map from `X'`. -/
theorem interiorCompactificationAmbientIso_interior :
    Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) ≫
        (interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower).hom =
      Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)) := by
  let D := CompDiagram.pullback X g C f' g' a b c h_upper h_lower
  let Q := compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)
  let E := interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower
  have hi : Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' D) ≫
      pullback.fst (Of.ι D.P_g) D.P_bar.obj.right.hom = f' :=
    CompDiagram.ιInterior_comp_toBase (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' D
  have hq : Of.ι Q ≫ pullback.fst b (CompDiagram.toBase X g C) = f' :=
    interiorLift_comp_toBase X.hom b f' c h_upper (ofInteriorHom X g C)
  have hqSource : Of.ι Q ≫ pullback.snd b (CompDiagram.toBase X g C) =
      c ≫ Of.ι (ofInteriorHom X g C) :=
    interiorLift_comp_toSource X.hom b f' c h_upper (ofInteriorHom X g C)
  have hbSource : Of.ι D.P_bar ≫
      pullback.snd (pullback.snd a C.P_g.obj.right.hom) C.P_bar.obj.right.hom = c ≫ Of.ι C.P_bar :=
    interiorLift_comp_toSource (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι (compactificationPullback g a g' b h_lower C.P_g)) c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower) C.P_bar
  apply nestedPullback_hom_ext C.P_bar.obj.right.hom (Of.ι C.P_g) b
  · refine Eq.trans ?_ hq.symm
    exact (Category.assoc _ _ _).trans ((congrArg
      (fun k => Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' D) ≫ k)
      (interiorCompactificationAmbientIso_over X g C f' g' a b c h_upper h_lower)).trans hi)
  · have hright : Of.ι Q ≫ pullback.snd b (CompDiagram.toBase X g C) ≫
        pullback.snd (Of.ι C.P_g) C.P_bar.obj.right.hom = c ≫ Of.ι C.P_bar :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ pullback.snd (Of.ι C.P_g) C.P_bar.obj.right.hom) hqSource).trans
          ((Category.assoc _ _ _).trans (congrArg (fun k => c ≫ k)
            (CompDiagram.ιInterior_comp_openImmersion X g C))))
    refine Eq.trans ?_ hright.symm
    have he := interiorAmbientIso_hom_snd_snd a C.P_g.obj.right.hom C.P_bar.obj.right.hom
      (Of.ι C.P_g) b (interiorLift g a g' b h_lower C.P_g)
      (interiorLift_comp_toSource g a g' b h_lower C.P_g)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' D) ≫ k) he).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ pullback.snd (pullback.snd a C.P_g.obj.right.hom)
            C.P_bar.obj.right.hom) (CompDiagram.ιInterior_comp_openImmersion (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' D)).trans
              hbSource)))

/-- The fixed-interior isomorphism identifying the two upper compactifications. -/
def interiorCompactificationIso :
    CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g'
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) ≅
    compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C) :=
  Of.isoMkOfAmbient (interiorCompactificationAmbientIso X g C f' g' a b c h_upper h_lower)
    (interiorCompactificationAmbientIso_interior X g C f' g' a b c h_upper h_lower)
    (interiorCompactificationAmbientIso_over X g C f' g' a b c h_upper h_lower)

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
end
end
