module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra

/-!
# Adic completion of ring deformations

Given a Noetherian `k`-algebra `P` and an ideal `J`, a deformation
`(A, Q) ⟶ (k, P)` completes to `(A, AdicCompletion J_Q Q) ⟶ (k, AdicCompletion J P)`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraCat

/-- Inverse image `J_Q = f⁻¹(J)` of `J` along the structure map of a deformation of `P`. -/
def adicCompletionIdeal {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : Ideal Q.algebra :=
  Ideal.comap f.toRingHom J

/-- The completion ideal is the comap of `J` along the underlying ring map. -/
theorem adicCompletionIdeal_eq_comap {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionIdeal J f = Ideal.comap f.toRingHom J := rfl

/-- Membership in the completion ideal is membership of the image in `J`. -/
theorem mem_adicCompletionIdeal {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) {x : Q.algebra} :
    x ∈ adicCompletionIdeal J f ↔ f.toRingHom x ∈ J := Iff.rfl

/-- The `J_Q`-adic completion of the algebra of a deformation of `P`. -/
abbrev adicCompletionAlgebra {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : Type u :=
  AdicCompletion (adicCompletionIdeal J f) Q.algebra

/-- The completed algebra has the adic-completion carrier of the original algebra. -/
theorem adicCompletionAlgebra_def {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionAlgebra J f = AdicCompletion (adicCompletionIdeal J f) Q.algebra := rfl

/-- Completing a Noetherian deformation along `J_Q` remains flat over the Artinian base. -/
instance instModuleFlat_adicCompletionAlgebra {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    Module.Flat Q.base.carrier (adicCompletionAlgebra J f) := sorry

/-- The completed pair `(A, Q^∧)` in the category of flat algebras. -/
def adicCompletionObj {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : FlatAlgebraCat Λ k :=
  of Q.base (adicCompletionAlgebra J f)

/-- Completing a deformation does not change the Artinian local base. -/
theorem adicCompletionObj_base {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionObj J f).base = Q.base := rfl

/-- The structure map of a deformation is adically continuous from `J_Q` to `J`. -/
def adicCompletion_adicContinuous {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    f.toRingHom.AdicContinuous (adicCompletionIdeal J f) J :=
  ⟨1, (pow_one (adicCompletionIdeal J f)).symm ▸ Ideal.map_comap_le⟩

/-- The canonical ring map `Q^∧ → P^∧` induced by a deformation of `P`. -/
def adicCompletionMap {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionAlgebra J f →+* AdicCompletion J P :=
  (adicCompletion_adicContinuous J f).completionMap

/-- The completion map extends the original structure map `Q → P`. -/
theorem adicCompletionMap_comp {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionMap J f).comp (algebraMap Q.algebra (adicCompletionAlgebra J f)) =
      (algebraMap P (AdicCompletion J P)).comp f.toRingHom :=
  (adicCompletion_adicContinuous J f).completionMap_comp

/-- The completed residue map commutes with the base algebra maps. -/
private theorem adicCompletionHom_commutes {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionMap J f).comp
        (algebraMap (adicCompletionObj J f).base.carrier (adicCompletionObj J f).algebra) =
      (algebraMap (ofResidue Λ k (AdicCompletion J P)).base.carrier
        (ofResidue Λ k (AdicCompletion J P)).algebra).comp f.baseHom.hom.toRingHom := sorry

/-- The canonical tensor lift of the completed residue map is bijective. -/
private theorem adicCompletionHom_isIsoTensor {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) :
    Function.Bijective (canonicalTensorMap
      (Q := adicCompletionObj J f) (P := ofResidue Λ k (AdicCompletion J P))
      f.baseHom (adicCompletionMap J f) (adicCompletionHom_commutes J f)) := sorry

/-- The completed residue arrow `(A, Q^∧) ⟶ (k, P^∧)`. -/
def adicCompletionHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionObj J f ⟶ ofResidue Λ k (AdicCompletion J P) :=
  Hom.of f.baseHom (adicCompletionMap J f)
    (by exact adicCompletionHom_commutes J f) (by exact adicCompletionHom_isIsoTensor J f)

/-- Completing a deformation keeps the same morphism of Artinian local bases. -/
theorem adicCompletionHom_baseHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionHom J f).baseHom = f.baseHom := rfl

/-- A morphism of deformations is adically continuous between the inverse images of `J`. -/
def adicCompletionMap_adicContinuous {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    g.left.toRingHom.AdicContinuous (adicCompletionIdeal J ξ.hom) (adicCompletionIdeal J η.hom) :=
  ⟨1, (pow_one (adicCompletionIdeal J ξ.hom)).symm ▸
    Ideal.map_le_iff_le_comap.mpr
      ((le_of_eq (congrArg (fun h ↦ Ideal.comap h.toRingHom J) g.w).symm).trans
        (le_of_eq (Ideal.comap_comap g.left.toRingHom η.hom.toRingHom).symm))⟩

/-- The completion of a deformation morphism commutes with the base algebra maps. -/
private theorem adicCompletionMapHom_commutes {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    (adicCompletionMap_adicContinuous J g).completionMap.comp
        (algebraMap (adicCompletionObj J ξ.hom).base.carrier
          (adicCompletionObj J ξ.hom).algebra) =
      (algebraMap (adicCompletionObj J η.hom).base.carrier
        (adicCompletionObj J η.hom).algebra).comp g.left.baseHom.hom.toRingHom := sorry

/-- The canonical tensor lift of a completed deformation morphism is bijective. -/
private theorem adicCompletionMapHom_isIsoTensor {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    Function.Bijective (canonicalTensorMap
      (Q := adicCompletionObj J ξ.hom) (P := adicCompletionObj J η.hom)
      g.left.baseHom (adicCompletionMap_adicContinuous J g).completionMap
      (adicCompletionMapHom_commutes J g)) := sorry

/-- The completed left arrow of a morphism of deformations. -/
def adicCompletionMapHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    adicCompletionObj J ξ.hom ⟶ adicCompletionObj J η.hom :=
  Hom.of g.left.baseHom (adicCompletionMap_adicContinuous J g).completionMap
    (by exact adicCompletionMapHom_commutes J g) (by exact adicCompletionMapHom_isIsoTensor J g)

/-- Completed deformation maps commute with the completed residue arrows. -/
private theorem adicCompletionMapHom_w {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    adicCompletionMapHom J g ≫ adicCompletionHom J η.hom =
      adicCompletionHom J ξ.hom := sorry

/-- Completion preserves identity maps of deformations. -/
private theorem adicCompletionMapHom_id {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    adicCompletionMapHom J (𝟙 ξ) = 𝟙 (adicCompletionObj J ξ.hom) := sorry

/-- Completion preserves composites of deformation maps. -/
private theorem adicCompletionMapHom_comp {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η ζ : deformationCategory Λ k P}
    (g : ξ ⟶ η) (h : η ⟶ ζ) :
    adicCompletionMapHom J (g ≫ h) =
      adicCompletionMapHom J g ≫ adicCompletionMapHom J h := sorry

variable (Λ k) in
/-- The functor from deformations of `P` to deformations of its `J`-adic completion. -/
def adicCompletionFunctor (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) :
    deformationCategory Λ k P ⥤ deformationCategory Λ k (AdicCompletion J P) where
  obj ξ := Over.mk (adicCompletionHom J ξ.hom)
  map g := Over.homMk (adicCompletionMapHom J g) (by exact adicCompletionMapHom_w J g)
  map_id ξ := by
    apply Over.OverMorphism.ext
    exact adicCompletionMapHom_id J ξ
  map_comp g h := by
    apply Over.OverMorphism.ext
    exact adicCompletionMapHom_comp J g h

/-- The completed deformation has left object `(A, Q^∧)`. -/
theorem adicCompletionFunctor_obj_left {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left = adicCompletionObj J ξ.hom := rfl

/-- The completed deformation has algebra the completion of `Q` along `J_Q`. -/
theorem adicCompletionFunctor_obj_algebra {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left.algebra = adicCompletionAlgebra J ξ.hom := rfl

/-- The completed deformation has the canonical completed residue arrow. -/
theorem adicCompletionFunctor_obj_hom {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).hom = adicCompletionHom J ξ.hom := rfl

variable (Λ k) in
/-- The projection from deformations of `P` to their Artinian local bases. -/
def deformationForget (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget

/-- The deformation projection sends a pair `(A, Q)` to the Artinian local algebra `A`. -/
theorem deformationForget_obj {P : Type u} [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForget Λ k P).obj ξ = ξ.left.base := rfl

/-- Completing deformations commutes with projection to the Artinian local base category. -/
theorem adicCompletionFunctor_comp_forget {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) :
    adicCompletionFunctor Λ k P J ⋙ deformationForget Λ k (AdicCompletion J P) =
      deformationForget Λ k P := sorry

variable (Λ k) in
/-- Adic completion as a functor of categories over the Artinian local base category. -/
def adicCompletionBasedFunctor (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (AdicCompletion J P)) where
  toFunctor := adicCompletionFunctor Λ k P J
  w := adicCompletionFunctor_comp_forget J

end FlatAlgebraCat
