/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Functor

/-!
# Fixed-degree relative projective quadruples

A fixed-degree quadruple consists of a morphism to the base, an invertible module on the source,
and a multiplicative family of maps from the corresponding Veronese pieces. This file also
records strict equivalence, pullback compatibility, and association with a degreewise relative
projective-spectrum functor.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
variable (d : ℕ)

/-- The degree-zero source of a Veronese map is the degree-zero homogeneous piece. -/
theorem RelativeProjDegreeQuadruple.sourceZeroSectionEq
    (U : S.Opens) (d : ℕ) :
    (Γ(𝒜 (Int.ofNat 0), U) : Type u) =
      (Γ(𝒜 (Int.ofNat (0 * d)), U) : Type u) := sorry

/-- Multiplication of Veronese pieces of indices `i` and `j` lands in index `i + j`. -/
theorem RelativeProjDegreeQuadruple.sourceMulSectionEq
    (U : S.Opens) (i j d : ℕ) :
    (Γ(𝒜 (Int.ofNat (i * d) + Int.ofNat (j * d)), U) : Type u) =
      (Γ(𝒜 (Int.ofNat ((i + j) * d)), U) : Type u) := sorry

/-- A fixed-degree relative projective quadruple over a test scheme. -/
structure RelativeProjDegreeQuadruple
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (d : ℕ) (T : Scheme.{u}) where
  /-- The structure morphism to the base scheme. -/
  morphism : T ⟶ S
  /-- The invertible module on the test scheme. -/
  lineBundle : T.Modules
  /-- Invertibility of the chosen module. -/
  lineBundle_invertible : Scheme.Modules.Invertible lineBundle
  /-- The degreewise components of the adjoint Veronese algebra map. -/
  psi :
    ∀ n : ℕ,
      𝒜 (Int.ofNat (n * d)) ⟶
        (Scheme.Modules.pushforward morphism).obj
          (RingedSpace.TensorPower.sheaf lineBundle n)
  /-- The degreewise map preserves the unit. -/
  psi_map_one :
    ∀ U : S.Opens,
      (((psi 0).val.app (op U)).hom)
          (Eq.mp (RelativeProjDegreeQuadruple.sourceZeroSectionEq 𝒜 U d)
            (𝒜.one (op U))) =
        TensorPower.oneSection T.sheaf lineBundle (op (morphism ⁻¹ᵁ U))
  /-- The degreewise map preserves multiplication. -/
  psi_map_mul :
    ∀ (U : S.Opens) (i j : ℕ)
      (x : Γ(𝒜 (Int.ofNat (i * d)), U))
      (y : Γ(𝒜 (Int.ofNat (j * d)), U)),
      (((psi (i + j)).val.app (op U)).hom
          (Eq.mp (RelativeProjDegreeQuadruple.sourceMulSectionEq 𝒜 U i j d)
            (𝒜.mul (op U) (Int.ofNat (i * d)) (Int.ofNat (j * d)) x y))) =
        TensorPower.mulSection T.sheaf lineBundle (op (morphism ⁻¹ᵁ U)) i j
          (((psi i).val.app (op U)).hom x)
          (((psi j).val.app (op U)).hom y)
  /-- The adjoint of the degree-one component. -/
  degreeOneMap :
    (Scheme.Modules.pullback morphism).obj (𝒜 (Int.ofNat (1 * d))) ⟶
      RingedSpace.TensorPower.sheaf lineBundle 1
  /-- The displayed degree-one map is adjoint to the degree-one component of `psi`. -/
  degreeOneMap_spec :
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).homEquiv
        (𝒜 (Int.ofNat (1 * d)))
        (RingedSpace.TensorPower.sheaf lineBundle 1)).toFun degreeOneMap = psi 1
  /-- The adjoint degree-one map is an epimorphism. -/
  degreeOne_surjective : Epi degreeOneMap

namespace RelativeProjDegreeQuadruple

open RingedSpace.TensorPower

/-- Construct a fixed-degree quadruple from its morphism, invertible module, graded map, and
compatibility conditions. -/
def of {T : Scheme.{u}}
    (morphism : T ⟶ S) (lineBundle : T.Modules)
    (lineBundle_invertible : Scheme.Modules.Invertible lineBundle)
    (psi : ∀ n : ℕ, 𝒜 (Int.ofNat (n * d)) ⟶
      (Scheme.Modules.pushforward morphism).obj
        (RingedSpace.TensorPower.sheaf lineBundle n))
    (psi_map_one : ∀ U : S.Opens,
      (((psi 0).val.app (op U)).hom
          (Eq.mp (sourceZeroSectionEq 𝒜 U d) (𝒜.one (op U)))) =
        TensorPower.oneSection T.sheaf lineBundle (op (morphism ⁻¹ᵁ U)))
    (psi_map_mul : ∀ (U : S.Opens) (i j : ℕ)
      (x : Γ(𝒜 (Int.ofNat (i * d)), U))
      (y : Γ(𝒜 (Int.ofNat (j * d)), U)),
      (((psi (i + j)).val.app (op U)).hom
          (Eq.mp (sourceMulSectionEq 𝒜 U i j d)
            (𝒜.mul (op U) (Int.ofNat (i * d)) (Int.ofNat (j * d)) x y))) =
        TensorPower.mulSection T.sheaf lineBundle (op (morphism ⁻¹ᵁ U)) i j
          (((psi i).val.app (op U)).hom x)
          (((psi j).val.app (op U)).hom y))
    (degreeOneMap :
      (Scheme.Modules.pullback morphism).obj (𝒜 (Int.ofNat (1 * d))) ⟶
        RingedSpace.TensorPower.sheaf lineBundle 1)
    (degreeOneMap_spec :
      ((Scheme.Modules.pullbackPushforwardAdjunction morphism).homEquiv
          (𝒜 (Int.ofNat (1 * d)))
          (RingedSpace.TensorPower.sheaf lineBundle 1)).toFun degreeOneMap = psi 1)
    (degreeOne_surjective : Epi degreeOneMap) :
    RelativeProjDegreeQuadruple 𝒜 d T where
  morphism := morphism
  lineBundle := lineBundle
  lineBundle_invertible := lineBundle_invertible
  psi := psi
  psi_map_one := psi_map_one
  psi_map_mul := psi_map_mul
  degreeOneMap := degreeOneMap
  degreeOneMap_spec := degreeOneMap_spec
  degreeOne_surjective := degreeOne_surjective

/-- The defining conditions of a fixed-degree quadruple hold simultaneously. -/
theorem conditions_spec {T : Scheme.{u}} (q : RelativeProjDegreeQuadruple 𝒜 d T) :
    Scheme.Modules.Invertible q.lineBundle ∧
      (∀ U : S.Opens,
        (((q.psi 0).val.app (op U)).hom
            (Eq.mp (sourceZeroSectionEq 𝒜 U d) (𝒜.one (op U)))) =
          TensorPower.oneSection T.sheaf q.lineBundle (op (q.morphism ⁻¹ᵁ U))) ∧
      (∀ (U : S.Opens) (i j : ℕ)
          (x : Γ(𝒜 (Int.ofNat (i * d)), U))
          (y : Γ(𝒜 (Int.ofNat (j * d)), U)),
        ((q.psi (i + j)).val.app (op U)).hom
            (Eq.mp (sourceMulSectionEq 𝒜 U i j d)
              (𝒜.mul (op U) (Int.ofNat (i * d)) (Int.ofNat (j * d)) x y)) =
          TensorPower.mulSection T.sheaf q.lineBundle (op (q.morphism ⁻¹ᵁ U)) i j
            (((q.psi i).val.app (op U)).hom x)
            (((q.psi j).val.app (op U)).hom y)) ∧
      (((Scheme.Modules.pullbackPushforwardAdjunction q.morphism).homEquiv
          (𝒜 (Int.ofNat (1 * d)))
          (RingedSpace.TensorPower.sheaf q.lineBundle 1)).toFun q.degreeOneMap = q.psi 1) ∧
      Epi q.degreeOneMap := sorry

/-- The degree-one epimorphism carried by a fixed-degree quadruple. -/
def degreeMap {T : Scheme.{u}} (q : RelativeProjDegreeQuadruple 𝒜 d T) :
    (Scheme.Modules.pullback q.morphism).obj (𝒜 (Int.ofNat (1 * d))) ⟶
      RingedSpace.TensorPower.sheaf q.lineBundle 1 :=
  q.degreeOneMap

/-- Pullback of a module sheaf commutes with its tensor powers once an explicit monoidal core is
supplied. -/
noncomputable def pullbackTensorPowerIsoOf
    {T T' : Scheme.{u}} (g : T' ⟶ T)
    (core : Scheme.Modules.pullbackPresheafCore g)
    (lineBundle : T.Modules) (n : ℕ) :
    (Scheme.Modules.pullback g).obj (RingedSpace.TensorPower.sheaf lineBundle n) ≅
      RingedSpace.TensorPower.sheaf
        ((Scheme.Modules.pullback g).obj lineBundle) n :=
  (Scheme.Modules.pullback g).mapIso
      (monoidalComparison.iso lineBundle n).symm ≪≫
    (@Functor.Monoidal.tensorPowerIso
      T.Modules T'.Modules _ _ _ _ (Scheme.Modules.pullback g)
      (Scheme.Modules.pullbackMonoidalOf g core) lineBundle n).symm ≪≫
      monoidalComparison.iso ((Scheme.Modules.pullback g).obj lineBundle) n

/-- The forward tensor-power pullback comparison is the composite of its three canonical
comparison maps. -/
theorem pullbackTensorPowerIsoOf_hom
    {T T' : Scheme.{u}} (g : T' ⟶ T)
    (core : Scheme.Modules.pullbackPresheafCore g)
    (lineBundle : T.Modules) (n : ℕ) :
    (pullbackTensorPowerIsoOf g core lineBundle n).hom =
      (Scheme.Modules.pullback g).map (monoidalComparison.iso lineBundle n).inv ≫
        (@Functor.Monoidal.tensorPowerIso
          T.Modules T'.Modules _ _ _ _ (Scheme.Modules.pullback g)
          (Scheme.Modules.pullbackMonoidalOf g core) lineBundle n).inv ≫
          (monoidalComparison.iso
            ((Scheme.Modules.pullback g).obj lineBundle) n).hom := sorry

/-- Two fixed-degree quadruples are strictly equivalent when their structure morphisms agree and
an isomorphism of line bundles intertwines every homogeneous component. -/
def StrictlyEquivalent
    {T : Scheme.{u}} (q q' : RelativeProjDegreeQuadruple 𝒜 d T) : Prop :=
  q.morphism = q'.morphism ∧
    ∃ lineBundleIso : q.lineBundle ≅ q'.lineBundle,
      ∀ n : ℕ,
        HEq
          (q.psi n ≫ (Scheme.Modules.pushforward q.morphism).map
            (RingedSpace.TensorPower.mapIso lineBundleIso n).hom)
          (q'.psi n)

/-- A quadruple is a pullback along `g` when its structure morphism and all adjoint homogeneous
maps agree with the explicit monoidal pullback construction. -/
def IsPullbackAlong
    {T T' : Scheme.{u}} (g : T' ⟶ T)
    (core : Scheme.Modules.pullbackPresheafCore g)
    (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (q' : RelativeProjDegreeQuadruple 𝒜 d T')
    (lineBundleIso : (Scheme.Modules.pullback g).obj q.lineBundle ≅ q'.lineBundle) : Prop :=
  q'.morphism = g ≫ q.morphism ∧
    ∀ n : ℕ,
      HEq
        (((Scheme.Modules.pullbackPushforwardAdjunction q'.morphism).homEquiv
          (𝒜 (Int.ofNat (n * d)))
          (RingedSpace.TensorPower.sheaf q'.lineBundle n)).symm (q'.psi n))
        (((Scheme.Modules.pullbackComp g q.morphism).inv.app
              (𝒜 (Int.ofNat (n * d)))) ≫
          (Scheme.Modules.pullback g).map
            (((Scheme.Modules.pullbackPushforwardAdjunction q.morphism).homEquiv
              (𝒜 (Int.ofNat (n * d)))
              (RingedSpace.TensorPower.sheaf q.lineBundle n)).symm (q.psi n)) ≫
          (pullbackTensorPowerIsoOf g core q.lineBundle n).hom ≫
          (RingedSpace.TensorPower.mapIso lineBundleIso n).hom)

/-- Degree-one pullback compatibility follows from degreewise pullback compatibility. -/
theorem IsPullbackAlong.degreeOneMap
    {T T' : Scheme.{u}} {g : T' ⟶ T}
    {core : Scheme.Modules.pullbackPresheafCore g}
    {q : RelativeProjDegreeQuadruple 𝒜 d T}
    {q' : RelativeProjDegreeQuadruple 𝒜 d T'}
    {lineBundleIso : (Scheme.Modules.pullback g).obj q.lineBundle ≅ q'.lineBundle}
    (h : IsPullbackAlong 𝒜 d g core q q' lineBundleIso) :
    HEq q'.degreeOneMap
      (((Scheme.Modules.pullbackComp g q.morphism).inv.app
            (𝒜 (Int.ofNat (1 * d)))) ≫
        (Scheme.Modules.pullback g).map q.degreeOneMap ≫
        (pullbackTensorPowerIsoOf g core q.lineBundle 1).hom ≫
        (RingedSpace.TensorPower.mapIso lineBundleIso 1).hom) := sorry

end RelativeProjDegreeQuadruple

namespace Scheme.RelativeProjDegreeFunctor

/-- A degreewise relative projective-spectrum functor is associated to fixed-degree quadruples
when its points are precisely strict-equivalence classes and its action is geometric pullback. -/
structure IsAssociatedToQuadruples
    (F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d) where
  /-- The relation between a functor point and a representative quadruple. -/
  associated :
    ∀ T : Scheme.{u},
      F_d.toFunctor.obj (op T) → RelativeProjDegreeQuadruple 𝒜 d T → Prop
  /-- Every functor point has a representative quadruple. -/
  exists_quadruple :
    ∀ (T : Scheme.{u}) (x : F_d.toFunctor.obj (op T)),
      ∃ q : RelativeProjDegreeQuadruple 𝒜 d T, associated T x q
  /-- Every quadruple represents a functor point. -/
  exists_point :
    ∀ (T : Scheme.{u}) (q : RelativeProjDegreeQuadruple 𝒜 d T),
      ∃ x : F_d.toFunctor.obj (op T), associated T x q
  /-- The structure morphism of a representative is its image in the base functor. -/
  base_eq :
    ∀ (T : Scheme.{u}) (x : F_d.toFunctor.obj (op T))
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      associated T x q → q.morphism = F_d.baseMap.app (op T) x
  /-- Equality of points is exactly strict equivalence of representatives. -/
  eq_iff :
    ∀ (T : Scheme.{u}) (x x' : F_d.toFunctor.obj (op T))
      (q q' : RelativeProjDegreeQuadruple 𝒜 d T),
      associated T x q → associated T x' q' →
        (x = x' ↔ RelativeProjDegreeQuadruple.StrictlyEquivalent 𝒜 d q q')
  /-- An explicit monoidal core for pullback along every morphism of test schemes. -/
  pullbackCore :
    ∀ (T T' : Scheme.{u}) (g : T' ⟶ T),
      Scheme.Modules.pullbackPresheafCore g
  /-- Pull back a representative quadruple along a morphism of test schemes. -/
  pullbackQuadruple :
    ∀ (T T' : Scheme.{u}) (g : T' ⟶ T)
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      RelativeProjDegreeQuadruple 𝒜 d T'
  /-- The structure morphism of the pulled-back quadruple is the composite. -/
  pullback_morphism_eq :
    ∀ (T T' : Scheme.{u}) (g : T' ⟶ T)
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      (pullbackQuadruple T T' g q).morphism = g ≫ q.morphism
  /-- The line bundle of the pulled-back quadruple is the module pullback. -/
  pullback_lineBundleIso :
    ∀ (T T' : Scheme.{u}) (g : T' ⟶ T)
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      (Scheme.Modules.pullback g).obj q.lineBundle ≅
        (pullbackQuadruple T T' g q).lineBundle
  /-- Every homogeneous map of the pulled-back quadruple is the geometric pullback. -/
  pullback_spec :
    ∀ (T T' : Scheme.{u}) (g : T' ⟶ T)
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      RelativeProjDegreeQuadruple.IsPullbackAlong 𝒜 d g (pullbackCore T T' g) q
        (pullbackQuadruple T T' g q) (pullback_lineBundleIso T T' g q)
  /-- The functor action is represented by pullback of quadruples. -/
  associated_pullback :
    ∀ (T T' : Scheme.{u}) (g : T' ⟶ T) (x : F_d.toFunctor.obj (op T))
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      associated T x q →
        associated T' (F_d.toFunctor.map (op g) x) (pullbackQuadruple T T' g q)

namespace IsAssociatedToQuadruples

/-- Pull back a representative quadruple using its associated functor data. -/
def pullback {F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (h : F_d.IsAssociatedToQuadruples)
    (T T' : Scheme.{u}) (g : T' ⟶ T)
    (q : RelativeProjDegreeQuadruple 𝒜 d T) :
    RelativeProjDegreeQuadruple 𝒜 d T' :=
  h.pullbackQuadruple T T' g q

/-- The point-representative correspondence and its pullback conditions hold simultaneously. -/
theorem conditions_spec {F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (h : F_d.IsAssociatedToQuadruples) :
    (∀ (T : Scheme.{u}) (x : F_d.toFunctor.obj (op T)),
      ∃ q : RelativeProjDegreeQuadruple 𝒜 d T, h.associated T x q) ∧
    (∀ (T : Scheme.{u}) (q : RelativeProjDegreeQuadruple 𝒜 d T),
      ∃ x : F_d.toFunctor.obj (op T), h.associated T x q) ∧
    (∀ (T : Scheme.{u}) (x : F_d.toFunctor.obj (op T))
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      h.associated T x q → q.morphism = F_d.baseMap.app (op T) x) ∧
    (∀ (T : Scheme.{u}) (x x' : F_d.toFunctor.obj (op T))
      (q q' : RelativeProjDegreeQuadruple 𝒜 d T),
      h.associated T x q → h.associated T x' q' →
        (x = x' ↔ RelativeProjDegreeQuadruple.StrictlyEquivalent 𝒜 d q q')) ∧
    (∀ (T T' : Scheme.{u}) (g : T' ⟶ T)
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      RelativeProjDegreeQuadruple.IsPullbackAlong 𝒜 d g (h.pullbackCore T T' g) q
        (pullback 𝒜 d h T T' g q) (h.pullback_lineBundleIso T T' g q)) ∧
    (∀ (T T' : Scheme.{u}) (g : T' ⟶ T) (x : F_d.toFunctor.obj (op T))
      (q : RelativeProjDegreeQuadruple 𝒜 d T),
      h.associated T x q →
        h.associated T' (F_d.toFunctor.map (op g) x) (pullback 𝒜 d h T T' g q)) := sorry

end IsAssociatedToQuadruples

end Scheme.RelativeProjDegreeFunctor

end AlgebraicGeometry
