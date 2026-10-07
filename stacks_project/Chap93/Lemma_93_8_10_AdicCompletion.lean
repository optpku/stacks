module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.RingTheory.AdicCompletion.Map
public import stacks_project.Chap93.Example_93_8_1_Rings_Category

/-!
# Adic completion of ring deformations

Given a Noetherian `k`-algebra `P` and an ideal `J`, a deformation
`(A, Q) ⟶ (k, P)` completes to `(A, AdicCompletion J_Q Q) ⟶ (k, AdicCompletion J P)`.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraCat

/-- Inverse image `J_Q = f⁻¹(J)` of `J` along the structure map of a deformation of `P`. -/
def adicCompletionIdeal {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : Ideal Q.algebra :=
  Ideal.comap f.toRingHom J

/-- `adicCompletionIdeal` is the comap of `J` along the underlying ring map. -/
theorem adicCompletionIdeal_eq_comap {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionIdeal J f = Ideal.comap f.toRingHom J := sorry

/-- Membership in `adicCompletionIdeal J f` is membership of the image in `J`. -/
theorem mem_adicCompletionIdeal {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) {x : Q.algebra} :
    x ∈ adicCompletionIdeal J f ↔ f.toRingHom x ∈ J := sorry

/-- The `J_Q`-adic completion of the algebra of a deformation of `P`. -/
abbrev adicCompletionAlgebra {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : Type u :=
  AdicCompletion (adicCompletionIdeal J f) Q.algebra

/-- Unfolding of `adicCompletionAlgebra`. -/
theorem adicCompletionAlgebra_def {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionAlgebra J f = AdicCompletion (adicCompletionIdeal J f) Q.algebra := sorry

/-- Completing a Noetherian deformation along `J_Q` remains flat over the Artinian base. -/
instance instModuleFlat_adicCompletionAlgebra {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    Module.Flat Q.base.carrier (adicCompletionAlgebra J f) := sorry

/-- The completed pair `(A, Q^∧)` in `FlatAlgebraCat`. -/
def adicCompletionObj {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : FlatAlgebraCat Λ k :=
  of Q.base (adicCompletionAlgebra J f)

/-- Completing a deformation does not change the Artinian local base. -/
theorem adicCompletionObj_base {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionObj J f).base = Q.base := sorry

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
      (algebraMap P (AdicCompletion J P)).comp f.toRingHom := sorry

/-- The completed residue arrow `(A, Q^∧) ⟶ (k, P^∧)`. -/
def adicCompletionHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionObj J f ⟶ ofResidue Λ k (AdicCompletion J P) :=
  Hom.of f.baseHom (adicCompletionMap J f) sorry sorry

/-- Completing a deformation keeps the same morphism of Artinian local bases. -/
theorem adicCompletionHom_baseHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionHom J f).baseHom = f.baseHom := sorry

/-- A morphism of deformations is adically continuous between the inverse images of `J`. -/
def adicCompletionMap_adicContinuous {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    g.left.toRingHom.AdicContinuous (adicCompletionIdeal J ξ.hom) (adicCompletionIdeal J η.hom) :=
  ⟨1, (pow_one (adicCompletionIdeal J ξ.hom)).symm ▸
    Ideal.map_le_iff_le_comap.mpr
      ((le_of_eq (congrArg (fun h ↦ Ideal.comap h.toRingHom J) g.w).symm).trans
        (le_of_eq (Ideal.comap_comap g.left.toRingHom η.hom.toRingHom).symm))⟩

/-- The completed left arrow of a morphism of deformations. -/
def adicCompletionMapHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    adicCompletionObj J ξ.hom ⟶ adicCompletionObj J η.hom :=
  Hom.of g.left.baseHom (adicCompletionMap_adicContinuous J g).completionMap sorry sorry

variable (Λ k) in
/-- The functor `Def_P ⥤ Def_{AdicCompletion J P}` sending `(A, Q)` to `(A, Q^∧)`. -/
def adicCompletionFunctor (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) :
    deformationCategory Λ k P ⥤ deformationCategory Λ k (AdicCompletion J P) where
  obj ξ := Over.mk (adicCompletionHom J ξ.hom)
  map g := Over.homMk (adicCompletionMapHom J g) sorry
  map_id := sorry
  map_comp := sorry

/-- The object map of `adicCompletionFunctor` has left object `(A, Q^∧)`. -/
theorem adicCompletionFunctor_obj_left {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left = adicCompletionObj J ξ.hom := sorry

/-- The object map of `adicCompletionFunctor` completes the algebra along `J_Q`. -/
theorem adicCompletionFunctor_obj_algebra {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left.algebra = adicCompletionAlgebra J ξ.hom := sorry

/-- The object map of `adicCompletionFunctor` has residue arrow `adicCompletionHom`. -/
theorem adicCompletionFunctor_obj_hom {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).hom = adicCompletionHom J ξ.hom := sorry

variable (Λ k) in
/-- The forgetful functor from `deformationCategory P` to `ArtinianLocalAlgCat`. -/
def deformationForget (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget

/-- `deformationForget` sends a deformation `(A, Q)` to the Artinian local algebra `A`. -/
theorem deformationForget_obj {P : Type u} [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForget Λ k P).obj ξ = ξ.left.base := sorry

/-- Completing deformations commutes with forgetting to `ArtinianLocalAlgCat`. -/
theorem adicCompletionFunctor_comp_forget {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) :
    adicCompletionFunctor Λ k P J ⋙ deformationForget Λ k (AdicCompletion J P) =
      deformationForget Λ k P := sorry

variable (Λ k) in
/-- The completion functor as a functor of categories over `C_Λ`. -/
def adicCompletionBasedFunctor (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (AdicCompletion J P)) where
  toFunctor := adicCompletionFunctor Λ k P J
  w := sorry

end FlatAlgebraCat
