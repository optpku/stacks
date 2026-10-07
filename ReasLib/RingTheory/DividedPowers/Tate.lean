module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Free

/-!
# Tate resolutions

This file connects chain differential graded algebras with the reusable divided-power API on
strictly graded-commutative nonnegative algebras.  A graded divided-power polynomial presentation
is characterized by its mapping property, so odd generators have exterior behavior and positive
even generators have divided-power behavior without imposing an ordinary commutative-ring
structure on the total graded object.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v w x y z

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A chain DGA has canonical base ring in degree zero when its structural scalar map is a
bijection onto the degree-zero piece. -/
@[stacks 09PN "degree zero of a Tate chain DGA is its base ring"]
def DegreeZeroIsBase (A : ChainDGAlgebra.{u, v} R) : Prop :=
  Function.Bijective A.nonnegativeAlgebraMap

end ChainDGAlgebra

namespace DividedPowerChainAlgebra.Hom

variable {R : Type u} [CommRing R]
variable {A B : DividedPowerChainAlgebra R}

/-- A divided-power chain-DGA homomorphism induces a prescribed canonical map on zeroth
homology. -/
@[stacks 09PP "prescribed map induced on zeroth homology"]
def InducesH0 (f : DividedPowerChainAlgebra.Hom A B)
    (f0 : A.toChainDGAlgebra.homologyZero →ₐ[R] B.toChainDGAlgebra.homologyZero) : Prop :=
  f.toChainHom.homologyZeroMap = f0

end DividedPowerChainAlgebra.Hom

namespace DividedPowerGradedAlgebra.FreePresentation

variable {R : Type u} [CommRing R]
variable {A B : DividedPowerChainAlgebra R}
variable {generators : ℕ → Type w}

/-- A map on zeroth homology lifts from a freely presented divided-power chain DGA into a target
with vanishing positive homology. -/
@[stacks 09PP]
theorem existsHom_liftingH0
    (P : FreePresentation A.toGradedAlgebra generators)
    (hB : B.toChainDGAlgebra.PositiveHomologyVanishes)
    (f0 : A.toChainDGAlgebra.homologyZero →ₐ[R] B.toChainDGAlgebra.homologyZero) :
    ∃ f : A ⟶ B, f.InducesH0 f0 := sorry

end DividedPowerGradedAlgebra.FreePresentation

/-- The graded generator family of a Tate algebra: `J` in degree zero and `V n` in every positive
degree `n`. -/
@[stacks 09PN "Tate generator indexing"]
def TateGenerators (J : Type v) (V : ℕ+ → Type v) : ℕ → Type v
  | 0 => J
  | n + 1 => V ⟨n + 1, Nat.succ_pos n⟩

/-- A Tate resolution relative to a chosen polynomial presentation.  Its underlying algebra is a
nonnegative strictly commutative chain DGA with compatible divided powers, its graded algebra is
free on the specified degree-zero and positive generators, and its augmentation is a genuine
quasi-isomorphism to the target in degree zero.  The base ring, the common universe of the
degree-zero and positive generator indices, and the target algebra may live in independent
universes. -/
@[stacks 09PN "Tate resolution"]
structure TateResolution {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {J : Type v} (pi0 : MvPolynomial J R →ₐ[R] S) where
  /-- The resolving divided-power chain DGA. -/
  algebra : DividedPowerChainAlgebra.{u, w} R
  /-- The positive-degree generators, indexed by their degree. -/
  positiveGenerators : ℕ+ → Type v
  /-- The free graded divided-power presentation. -/
  presentation : DividedPowerGradedAlgebra.FreePresentation algebra.toGradedAlgebra
    (TateGenerators J positiveGenerators)
  /-- The augmentation to the target algebra concentrated in degree zero. -/
  augmentation : ChainDGAlgebra.Augmentation algebra.toChainDGAlgebra S
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso augmentation.toChainMap
  /-- On the chosen degree-zero generators, the augmentation is the polynomial presentation. -/
  augmentation_generator (j : J) :
    (ChainDGAlgebra.degreeZeroIso R S).hom
        (augmentation.toChainMap.f 0 (presentation.generator 0 j)) =
      pi0 (MvPolynomial.X j)

attribute [instance] TateResolution.quasiIso

namespace TateResolution

section Positive

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]

/-- Reindex a polynomial presentation with no degree-zero variables by the universe lift of the
empty index type. -/
@[stacks 09PN "universe lift of an empty polynomial presentation"]
def liftEmptyPresentation (pi0 : MvPolynomial Empty R →ₐ[R] S) :
    MvPolynomial (ULift.{x, 0} Empty) R →ₐ[R] S :=
  pi0.comp (MvPolynomial.renameEquiv R
    (Equiv.ulift : ULift.{x, 0} Empty ≃ Empty)).toAlgHom

/-- Evaluation of the lifted empty presentation is evaluation after the canonical polynomial
renaming. -/
@[simp, stacks 09PN "evaluation of a lifted empty polynomial presentation"]
theorem liftEmptyPresentation_apply
    (pi0 : MvPolynomial Empty R →ₐ[R] S)
    (p : MvPolynomial (ULift.{x, 0} Empty) R) :
    liftEmptyPresentation pi0 p =
      pi0 (MvPolynomial.renameEquiv R
        (Equiv.ulift : ULift.{x, 0} Empty ≃ Empty) p) := sorry

/-- Universe lifting an empty polynomial presentation preserves and reflects surjectivity. -/
@[stacks 09PN "surjectivity of a lifted empty polynomial presentation"]
theorem liftEmptyPresentation_surjective_iff
    (pi0 : MvPolynomial Empty R →ₐ[R] S) :
    Function.Surjective (liftEmptyPresentation.{u, w, x} pi0) ↔
      Function.Surjective pi0 := sorry

/-- A positive-generator Tate resolution with positive generator types in an arbitrary universe.
The degree-zero presentation has no variables and is reindexed by `ULift Empty`. -/
@[stacks 09PN "positive-generator Tate resolution in an arbitrary universe"]
abbrev Positive (pi0 : MvPolynomial Empty R →ₐ[R] S) :=
  TateResolution.{u, x, w} (liftEmptyPresentation pi0)

end Positive

section Model

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] S}

/-- A Tate resolution has finitely many positive generators degreewise. -/
@[stacks 09PN "finite positive generators of a Tate resolution"]
def HasFinitePositiveGenerators (A : TateResolution.{u, v, w} pi0) : Prop :=
  ∀ n : ℕ+, Finite (A.positiveGenerators n)

/-- If the polynomial presentation has no degree-zero variables, the structural scalar map
identifies the base ring with degree zero of the resolving algebra. -/
@[stacks 09PN "degree zero of a positive-generator Tate resolution"]
theorem degreeZeroIsBase [IsEmpty J] (A : TateResolution.{u, v, w} pi0) :
    A.algebra.toChainDGAlgebra.DegreeZeroIsBase := sorry

end Model

section Existence

variable {R : Type u} {S : Type w} {J : Type v}
  [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 23.6.9: every surjective polynomial presentation admits a Tate resolution with
independent base, generator, and target universes. -/
@[stacks 09PN "(1)"]
theorem nonempty (pi0 : MvPolynomial J R →ₐ[R] S) (hpi0 : Function.Surjective pi0) :
    Nonempty (TateResolution.{u, v, w} pi0) := sorry

end Existence

section FiniteExistence

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {J : Type v}

/-- Over a Noetherian base and for a finite-type target, a Tate resolution may be chosen with
finitely many positive generators in every degree.  The finite presentation index type and target
ring may live in separate universes. -/
@[stacks 09PN "(2), fixed presentation"]
theorem exists_finite [IsNoetherianRing R] [Algebra.FiniteType R S]
    [Finite J]
    (pi0 : MvPolynomial J R →ₐ[R] S) (hpi0 : Function.Surjective pi0) :
    ∃ A : TateResolution.{u, v, w} pi0, A.HasFinitePositiveGenerators := sorry

/-- Over a Noetherian base, a finite-type algebra admits a finite polynomial presentation and a
Tate resolution with finitely many generators in every positive degree. -/
@[stacks 09PN "(2), finite presentation"]
theorem exists_finitePresentation [IsNoetherianRing R] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (pi0 : MvPolynomial (Fin n) R →ₐ[R] S),
      Function.Surjective pi0 ∧
        ∃ A : TateResolution.{u, 0, w} pi0, A.HasFinitePositiveGenerators := sorry

end FiniteExistence

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] S}

/-- A morphism of Tate resolutions over a specified map of their ordinary augmentation targets.
The divided-power chain-DGA map is explicit data, and its augmentation square is required to
commute on canonical zeroth homology. -/
@[stacks 0GZ5 "morphism of Tate resolutions over an algebra map"]
structure Hom
    {T : Type w} [CommRing T] [Algebra R T]
    {K : Type x} {pi0' : MvPolynomial K R →ₐ[R] T}
    (A : TateResolution.{u, v, w} pi0) (sigma : S →ₐ[R] T)
    (B : TateResolution.{u, x, w} pi0') where
  /-- The divided-power chain-DGA map between the resolutions. -/
  toHom : A.algebra ⟶ B.algebra
  /-- The induced square on canonical zeroth homology commutes over `sigma`. -/
  commutesOnH0 :
    toHom.toChainHom.CommutesOnH0Over sigma A.augmentation B.augmentation

namespace Hom

variable {A : TateResolution.{u, v, w} pi0}
variable {T U : Type w} [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
variable {K : Type x} {L : Type y}
variable {pi0' : MvPolynomial K R →ₐ[R] T}
variable {pi0'' : MvPolynomial L R →ₐ[R] U}
variable {B : TateResolution.{u, x, w} pi0'}
variable {C : TateResolution.{u, y, w} pi0''}
variable {sigma : S →ₐ[R] T} {tau : T →ₐ[R] U}

/-- Bundle an explicit divided-power chain-DGA map over a specified target-algebra map. -/
def of (f : A.algebra ⟶ B.algebra)
    (hf : f.toChainHom.CommutesOnH0Over sigma A.augmentation B.augmentation) :
    TateResolution.Hom A sigma B where
  toHom := f
  commutesOnH0 := hf

/-- The divided-power chain-DGA map underlying `Hom.of` is the supplied map. -/
@[simp]
theorem of_toHom (f : A.algebra ⟶ B.algebra)
    (hf : f.toChainHom.CommutesOnH0Over sigma A.augmentation B.augmentation) :
    (of f hf).toHom = f := sorry

/-- Tate-resolution morphisms over a fixed target map are determined by their chain-DGA map. -/
@[ext]
theorem ext {f g : TateResolution.Hom A sigma B} (h : f.toHom = g.toHom) :
    f = g := sorry

/-- Any morphism of augmentation targets lifts to a morphism between supplied Tate resolutions.
The lift is not canonical, so the reusable statement exposes existence while `Hom` remains the
explicit data owner. -/
@[stacks 0GZ5 "existence of a Tate-resolution morphism over an algebra map"]
theorem nonempty (A : TateResolution.{u, v, w} pi0) (sigma : S →ₐ[R] T)
    (B : TateResolution.{u, x, w} pi0') :
    Nonempty (TateResolution.Hom A sigma B) := sorry

/-- The identity morphism of a Tate resolution lies over the identity of its target algebra. -/
def id (A : TateResolution.{u, v, w} pi0) :
    TateResolution.Hom A (AlgHom.id R S) A where
  toHom := DividedPowerChainAlgebra.Hom.id A.algebra
  commutesOnH0 := ChainDGAlgebra.Hom.commutesOnH0Over_id A.augmentation

/-- The divided-power chain-DGA map underlying the identity Tate morphism is the identity. -/
@[simp]
theorem id_toHom (A : TateResolution.{u, v, w} pi0) :
    (id A).toHom = DividedPowerChainAlgebra.Hom.id A.algebra := sorry

/-- Composition of Tate-resolution morphisms, lying over composition of the target maps. -/
def comp (g : TateResolution.Hom B tau C) (f : TateResolution.Hom A sigma B) :
    TateResolution.Hom A (tau.comp sigma) C where
  toHom := DividedPowerChainAlgebra.Hom.comp g.toHom f.toHom
  commutesOnH0 := ChainDGAlgebra.Hom.commutesOnH0Over_comp
    f.commutesOnH0 g.commutesOnH0

/-- The divided-power chain-DGA map underlying a composite Tate morphism is the composite map. -/
@[simp]
theorem comp_toHom (g : TateResolution.Hom B tau C)
    (f : TateResolution.Hom A sigma B) :
    (comp g f).toHom = DividedPowerChainAlgebra.Hom.comp g.toHom f.toHom := sorry

/-- A Tate-resolution morphism forgets to a morphism of its underlying augmented chain DGAs. -/
def toAugmentationHom (f : TateResolution.Hom A sigma B) :
    ChainDGAlgebra.Augmentation.Hom A.augmentation B.augmentation where
  toChainHom := f.toHom.toChainHom
  toAlgHom := sigma
  commutesOnH0 := f.commutesOnH0

/-- The chain-DGA component of the underlying augmented morphism is the underlying Tate map. -/
@[simp]
theorem toAugmentationHom_toChainHom (f : TateResolution.Hom A sigma B) :
    f.toAugmentationHom.toChainHom = f.toHom.toChainHom := sorry

/-- The target-algebra component of the underlying augmented morphism is the specified map. -/
@[simp]
theorem toAugmentationHom_toAlgHom (f : TateResolution.Hom A sigma B) :
    f.toAugmentationHom.toAlgHom = sigma := sorry

/-- Forgetting the identity Tate morphism gives the identity augmented chain-DGA morphism. -/
@[simp]
theorem id_toAugmentationHom (A : TateResolution.{u, v, w} pi0) :
    (id A).toAugmentationHom =
      ChainDGAlgebra.Augmentation.Hom.id A.augmentation := sorry

/-- Forgetting a composite Tate morphism gives the composite augmented morphism. -/
@[simp]
theorem comp_toAugmentationHom (g : TateResolution.Hom B tau C)
    (f : TateResolution.Hom A sigma B) :
    (comp g f).toAugmentationHom =
      ChainDGAlgebra.Augmentation.Hom.comp g.toAugmentationHom f.toAugmentationHom := sorry

/-- Composing with the identity on the source leaves a Tate morphism unchanged. -/
@[simp]
theorem id_comp (f : TateResolution.Hom A sigma B) :
    comp f (id A) = f := sorry

/-- Composing with the identity on the target leaves a Tate morphism unchanged. -/
@[simp]
theorem comp_id (f : TateResolution.Hom A sigma B) :
    comp (id B) f = f := sorry

/-- Composition of Tate-resolution morphisms is associative. -/
theorem assoc
    {V : Type w} [CommRing V] [Algebra R V]
    {M : Type z} {pi0''' : MvPolynomial M R →ₐ[R] V}
    {D : TateResolution.{u, z, w} pi0'''} {upsilon : U →ₐ[R] V}
    (h : TateResolution.Hom C upsilon D)
    (g : TateResolution.Hom B tau C) (f : TateResolution.Hom A sigma B) :
    comp h (comp g f) = comp (comp h g) f := sorry

end Hom

/-- Any two Tate resolutions of the same target admit a morphism over the identity target map.
This is the canonical comparison-map interface used by resolution-independence arguments. -/
@[stacks 09PQ "comparison of Tate resolutions over the identity"]
theorem Hom.nonempty_over_id
    (A : TateResolution.{u, v, w} pi0)
    {J' : Type x} {pi0' : MvPolynomial J' R →ₐ[R] S}
    (B : TateResolution.{u, x, w} pi0') :
    Nonempty (TateResolution.Hom A (AlgHom.id R S) B) := sorry

end TateResolution
