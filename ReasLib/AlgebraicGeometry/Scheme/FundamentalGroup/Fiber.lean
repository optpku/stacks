/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PreGaloisCategory
open CategoryTheory.Functor
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The set-valued finite étale fiber is the actual functor of lifts of the
separably closed point, expressed in the slice category. -/
def finiteEtaleFiberType (s : Spec (.of Ω) ⟶ X) : FiniteEtale X ⥤ Type u :=
  MorphismProperty.Over.forget finiteEtaleMorphism ⊤ X ⋙ coyoneda.obj (op (Over.mk s))

set_option backward.isDefEq.respectTransparency false in
/-- A finite étale scheme has a finite fiber at a separably closed point. -/
instance finiteEtaleFiberType_finite (s : Spec (.of Ω) ⟶ X) (V : FiniteEtale X) :
    Finite ((finiteEtaleFiberType s).obj V) := by
  letI : IsFinite V.hom := V.prop.1
  let P := pullback V.hom s
  let g : P ⟶ Spec (.of Ω) := pullback.snd V.hom s
  let R : CommRingCat := Γ(Spec (.of Ω), ⊤)
  let A : CommRingCat := Γ(P, ⊤)
  letI : Algebra R A := g.appTop.hom.toAlgebra
  letI : Algebra R Ω := (Scheme.ΓSpecIso (.of Ω)).hom.hom.toAlgebra
  letI : Module.Finite R A := (RingHom.finite_algebraMap).mp g.finite_appTop
  -- Lifts give sections of the actual pullback, hence algebra maps to Ω.
  let lift (t : Over.mk s ⟶ Over.mk V.hom) : Spec (.of Ω) ⟶ P :=
    pullback.lift t.left (𝟙 _) (by simpa using Over.w t)
  have lift_fac (t : Over.mk s ⟶ Over.mk V.hom) : lift t ≫ g = 𝟙 _ :=
    pullback.lift_snd _ _ _
  let E : (Over.mk s ⟶ Over.mk V.hom) → (A →ₐ[R] Ω) := fun t ↦
    { toRingHom := (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp (lift t).appTop.hom
      commutes' := by
        intro r
        change (Scheme.ΓSpecIso (.of Ω)).hom ((lift t).appTop (g.appTop r)) =
          (Scheme.ΓSpecIso (.of Ω)).hom r
        congr 1
        exact ConcreteCategory.congr_hom
          (by simpa using congrArg Scheme.Hom.appTop (lift_fac t)) r }
  apply Finite.of_injective E
  intro a b hab
  have hlift : lift a = lift b := by
    apply ext_of_isAffine
    ext r
    exact (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective
      (AlgHom.congr_fun hab r)
  apply Over.OverMorphism.ext
  simpa [lift] using congrArg (fun l : Spec (.of Ω) ⟶ P ↦ l ≫ pullback.fst V.hom s) hlift

/-- The finite-set fiber functor retains the actual scheme-valued lifts. -/
def finiteEtaleFiberAt [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) : FiniteEtale X ⥤ FintypeCat.{u} where
  obj V := FintypeCat.of ((finiteEtaleFiberType s).obj V)
  map a := FintypeCat.homMk ((finiteEtaleFiberType s).map a)
  map_id V := by
    ext x
    exact ConcreteCategory.congr_hom ((finiteEtaleFiberType s).map_id V) x
  map_comp a b := by
    ext x
    exact ConcreteCategory.congr_hom ((finiteEtaleFiberType s).map_comp a b) x

/-- The étale fundamental group is the automorphism group of the actual
finite étale fiber functor, with its canonical profinite topology. -/
abbrev fundamentalGroup [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) := Aut (finiteEtaleFiberAt s)

/-- Base change identifies geometric lifts through the actual slice
map/pullback adjunction, not through equality of the two fiber functors. -/
def finiteEtaleFiberBaseChangeEquiv (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    (V : FiniteEtale Y) :
    (finiteEtaleFiberType s).obj ((finiteEtaleBaseChange f).obj V) ≃
      (finiteEtaleFiberType (s ≫ f)).obj V :=
  ((Over.mapPullbackAdj f).homEquiv (Over.mk s) (Over.mk V.hom)).symm

/-- The finite étale base-change comparison has the explicit adjunction
equivalence on each geometric fiber. -/
def finiteEtaleFiberBaseChangeIso [IsSepClosed Ω] (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X) :
    finiteEtaleBaseChange f ⋙ finiteEtaleFiberAt s ≅ finiteEtaleFiberAt (s ≫ f) :=
  NatIso.ofComponents (fun V ↦
    { hom := FintypeCat.homMk (finiteEtaleFiberBaseChangeEquiv f s V)
      inv := FintypeCat.homMk (finiteEtaleFiberBaseChangeEquiv f s V).symm
      hom_inv_id := by
        ext x
        exact (finiteEtaleFiberBaseChangeEquiv f s V).symm_apply_apply x
      inv_hom_id := by
        ext x
        exact (finiteEtaleFiberBaseChangeEquiv f s V).apply_symm_apply x }) (by
    intro V W a
    ext x
    exact (Over.mapPullbackAdj f).homEquiv_naturality_right_symm x
      ((MorphismProperty.Over.forget finiteEtaleMorphism ⊤ Y).map a))

namespace Hom

/-- A scheme morphism induces a fundamental-group homomorphism by
whiskering with finite étale base change and the specified fiber comparison. -/
def fundamentalGroupMap [IsSepClosed Ω] (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X) :
    ContinuousMonoidHom (Scheme.fundamentalGroup s) (Scheme.fundamentalGroup (s ≫ f)) where
  toFun a := (finiteEtaleFiberBaseChangeIso f s).conjAut
    (((whiskeringLeft (FiniteEtale Y) (FiniteEtale X) FintypeCat).obj
      (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberAt s) a)
  map_one' := ((finiteEtaleFiberBaseChangeIso f s).conjAut.toMonoidHom.comp
    (((whiskeringLeft (FiniteEtale Y) (FiniteEtale X) FintypeCat).obj
      (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberAt s))).map_one
  map_mul' := ((finiteEtaleFiberBaseChangeIso f s).conjAut.toMonoidHom.comp
    (((whiskeringLeft (FiniteEtale Y) (FiniteEtale X) FintypeCat).obj
      (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberAt s))).map_mul
  continuous_toFun := by
    rw [Topology.IsInducing.continuous_iff
      (autEmbedding_isClosedEmbedding _).isInducing, continuous_pi_iff]
    intro V
    change Continuous fun a : Scheme.fundamentalGroup s ↦
      ((finiteEtaleFiberBaseChangeIso f s).app V).conjAut
        (autEmbedding (finiteEtaleFiberAt s) a ((finiteEtaleBaseChange f).obj V))
    exact continuous_of_discreteTopology.comp
      ((continuous_apply _).comp continuous_induced_dom)

/-- The induced homomorphism is the conjugate of the actual whiskered
automorphism under the specified geometric fiber comparison. -/
theorem fundamentalGroupMap_apply [IsSepClosed Ω] (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    (a : Scheme.fundamentalGroup s) :
    fundamentalGroupMap f s a = (finiteEtaleFiberBaseChangeIso f s).conjAut
      (((whiskeringLeft (FiniteEtale Y) (FiniteEtale X) FintypeCat).obj
        (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberAt s) a) := rfl

end Hom
end AlgebraicGeometry.Scheme
