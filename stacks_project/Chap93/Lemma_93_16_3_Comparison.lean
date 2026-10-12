/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import ReasLib.RingTheory.AdicCompletion.Map
public import stacks_project.Chap90.Definition_90_12_1_DualNumber
public import stacks_project.Chap93.Lemma_93_16_3_Stalk

/-!
# Isolated-singularity comparison maps of scheme deformation categories

The three maps
`Def_X ⥤ᵇ ∏ Def_{O_{X, p i}} ⥤ᵇ ∏ Def_{O_{X, p i}^h} ⥤ᵇ ∏ Def_{O_{X, p i}^∧}`
are assembled from stalk functors, pair henselization, and hensel-to-complete
comparison over the residue object of Definition 90.16.8.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing RingPairCat
open scoped BasedFunctor

universe u

noncomputable section

namespace CategoryTheory.BasedFunctor

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type (u + 1)} [Category.{u} F] [Category.{u} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

/-- The differential of a based functor is the map on isomorphism classes of
dual-number fibres. -/
def differential (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    isomorphismClasses.obj (Cat.of (p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k))) →
      isomorphismClasses.obj (Cat.of (q.Fiber (ArtinianLocalAlgCat.dualNumber Λ k))) :=
  (φ.fiberFunctor (ArtinianLocalAlgCat.dualNumber Λ k)).isoClassesMap

end CategoryTheory.BasedFunctor

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {ι : Type u}

/-- The finite product of ring deformation categories over `ArtinianLocalAlgCat`,
with objects `(A, x i)` where each `x i` is a deformation of `R i` over the same
base `A`. -/
def deformationPi (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    Type (u + 1) :=
  (A : ArtinianLocalAlgCat Λ k) × ∀ i, (deformationForget Λ k (R i)).Fiber A

variable {R : ι → Type u} [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]

/-- Morphisms in `deformationPi` are a base map together with a family of
deformation morphisms. -/
def deformationPiHom (X Y : deformationPi Λ k R) : Type u :=
  (f : X.1 ⟶ Y.1) ×
    ∀ i, { φ : Fiber.fiberInclusion.obj (X.2 i) ⟶ Fiber.fiberInclusion.obj (Y.2 i) //
      (deformationForget Λ k (R i)).map φ =
        eqToHom (X.2 i).property ≫ f ≫ eqToHom (Y.2 i).property.symm }

/-- The identity morphism of an equibased family of deformations. -/
def deformationPiHom.id (X : deformationPi Λ k R) : deformationPiHom Λ k X X :=
  ⟨𝟙 X.1, fun i ↦ ⟨𝟙 (Fiber.fiberInclusion.obj (X.2 i)), sorry⟩⟩

/-- Composition of morphisms of equibased families of deformations. -/
def deformationPiHom.comp {X Y Z : deformationPi Λ k R} (f : deformationPiHom Λ k X Y)
    (g : deformationPiHom Λ k Y Z) : deformationPiHom Λ k X Z :=
  ⟨f.1 ≫ g.1, fun i ↦ ⟨(f.2 i).1 ≫ (g.2 i).1, sorry⟩⟩

/-- The category of equibased families of ring deformations. -/
instance : Category.{u} (deformationPi Λ k R) where
  Hom := deformationPiHom Λ k
  id := deformationPiHom.id Λ k
  comp f g := deformationPiHom.comp Λ k f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

variable (R) in
/-- The projection `∏_{C_Λ} Def_{R i} ⥤ C_Λ` sending `(A, x i)` to `A`. -/
def deformationPiForget : deformationPi Λ k R ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.1
  map f := f.1
  map_id := sorry
  map_comp := sorry

variable (R) in
/-- The slice projection of `deformationPi` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationPiForget_op :
    IsFibered.InGroupoids (deformationPiForget Λ k R).op :=
  sorry

variable (R) in
/-- The based functor projecting `∏_{C_Λ} Def_{R i}` onto the factor `Def_{R i}`. -/
def evalBasedFunctor (i : ι) :
    BasedCategory.ofFunctor (deformationPiForget Λ k R) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (R i)) where
  toFunctor :=
    { obj X := Fiber.fiberInclusion.obj (X.2 i)
      map f := (f.2 i).1
      map_id := sorry
      map_comp := sorry }
  w := sorry

variable (R) in
/-- Pair a family of based functors into `Def_{R i}` over a common projection `p`
into a single based functor landing in `deformationPi`. -/
def pairing {F : Type (u + 1)} [Category.{u} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (φ : ∀ i, BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (deformationForget Λ k (R i))) :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (deformationPiForget Λ k R) where
  toFunctor :=
    { obj x := ⟨p.obj x, fun i ↦ ⟨(φ i).obj x, (φ i).w_obj x⟩⟩
      map f := ⟨p.map f, fun i ↦ ⟨(φ i).map f, sorry⟩⟩
      map_id := sorry
      map_comp := sorry }
  w := sorry

variable (R) in
/-- Apply a family of based functors `Def_{R i} ⥤ᵇ Def_{S i}` factorwise to
`deformationPi`. -/
def deformationPiMap (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)]
    (φ : ∀ i, BasedCategory.ofFunctor (deformationForget Λ k (R i)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (S i))) :
    BasedCategory.ofFunctor (deformationPiForget Λ k R) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k S) where
  toFunctor :=
    { obj X := ⟨X.1, fun i ↦ ⟨(φ i).obj (Fiber.fiberInclusion.obj (X.2 i)),
        ((φ i).w_obj (Fiber.fiberInclusion.obj (X.2 i))).trans (X.2 i).property⟩⟩
      map f := ⟨f.1, fun i ↦ ⟨(φ i).map (f.2 i).1, sorry⟩⟩
      map_id := sorry
      map_comp := sorry }
  w := sorry

end FlatAlgebraCat

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable [henselianPairInclusion.IsRightAdjoint]
variable (P : Type u) [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P]

/-- Inverse image of the maximal ideal along a deformation of `P`. -/
def comapMaximalIdeal (x : deformationCategory Λ k P) : Ideal x.left.algebra :=
  Ideal.comap x.hom.toRingHom (maximalIdeal P)

/-- Pair morphism `(Q, m_Q) ⟶ (P, m)` induced by a deformation of `P`. -/
def objPairHom (x : deformationCategory Λ k P) :
    pairOfIdeal (comapMaximalIdeal Λ k P x) ⟶ pairOfIdeal (maximalIdeal P) :=
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom x.hom.toRingHom)
      (CommRingCat.ofHom
        (Ideal.quotientMap (maximalIdeal P) x.hom.toRingHom
          (le_rfl : comapMaximalIdeal Λ k P x ≤ Ideal.comap x.hom.toRingHom (maximalIdeal P))))
      (pairOfIdeal_hom_square_of_ringHom (comapMaximalIdeal Λ k P x) (maximalIdeal P)
        x.hom.toRingHom le_rfl)

/-- The henselization ring `Q^h` of the inverse-image pair. -/
abbrev objHenselizationRing (x : deformationCategory Λ k P) : Type u :=
  henselizationRing (pairOfIdeal (comapMaximalIdeal Λ k P x))

/-- The henselization `Q^h` is an `A`-algebra via `A → Q → Q^h`. -/
instance instAlgebra_objHenselizationRing (x : deformationCategory Λ k P) :
    Algebra x.left.base.carrier (objHenselizationRing Λ k P x) :=
  (RingHom.comp (toHenselization (pairOfIdeal (comapMaximalIdeal Λ k P x)))
      (algebraMap x.left.base.carrier x.left.algebra)).toAlgebra

/-- `Q^h` is flat over `A`. -/
instance instModuleFlat_objHenselizationRing (x : deformationCategory Λ k P) :
    Module.Flat x.left.base.carrier (objHenselizationRing Λ k P x) :=
  sorry

/-- The `k`-algebra structure on `P^h` via `k → P → P^h`. -/
instance instAlgebra_k_henselizationRing :
    Algebra k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) :=
  (RingHom.comp (toHenselization (pairOfIdeal (maximalIdeal P))) (algebraMap k P)).toAlgebra

/-- The object `(A, Q^h)` attached to a deformation of `P`. -/
def objHenselization (x : deformationCategory Λ k P) : FlatAlgebraCat Λ k :=
  of x.left.base (objHenselizationRing Λ k P x)

/-- The morphism `(A, Q^h) ⟶ (k, P^h)` attached to a deformation of `P`. -/
def objHenselizationHom (x : deformationCategory Λ k P) :
    objHenselization Λ k P x ⟶
      ofResidue Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) where
  baseHom := x.hom.baseHom
  toRingHom := henselizationRingMap (objPairHom Λ k P x)
  commutes := sorry
  isIso_tensor := sorry

/-- A morphism of deformations carries inverse-image maximal ideals. -/
theorem mapPairHom_ideal_le {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    comapMaximalIdeal Λ k P x ≤
      Ideal.comap f.left.toRingHom (comapMaximalIdeal Λ k P y) :=
  sorry

/-- Pair morphism induced by a morphism of deformations. -/
def mapPairHom {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    pairOfIdeal (comapMaximalIdeal Λ k P x) ⟶ pairOfIdeal (comapMaximalIdeal Λ k P y) :=
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom f.left.toRingHom)
      (CommRingCat.ofHom
        (Ideal.quotientMap (comapMaximalIdeal Λ k P y) f.left.toRingHom
          (mapPairHom_ideal_le Λ k P f)))
      (pairOfIdeal_hom_square_of_ringHom (comapMaximalIdeal Λ k P x)
        (comapMaximalIdeal Λ k P y) f.left.toRingHom (mapPairHom_ideal_le Λ k P f))

/-- The morphism `(A, Q^h) ⟶ (A', Q'^h)` induced by a morphism of deformations. -/
def mapHenselizationHom {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    objHenselization Λ k P x ⟶ objHenselization Λ k P y where
  baseHom := f.left.baseHom
  toRingHom := henselizationRingMap (mapPairHom Λ k P f)
  commutes := sorry
  isIso_tensor := sorry

/-- The natural functor `Def_P ⥤ Def_{P^h}` induced by pair henselization. -/
def henselizationFunctor :
    deformationCategory Λ k P ⥤
      deformationCategory Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) where
  obj x := Over.mk (objHenselizationHom Λ k P x)
  map f := Over.homMk (mapHenselizationHom Λ k P f) sorry
  map_id := sorry
  map_comp := sorry

/-- Pair henselization of deformations commutes with forgetting to `C_Λ`. -/
theorem henselizationFunctor_comp_forget :
    henselizationFunctor Λ k P ⋙
        deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) =
      deformationForget Λ k P :=
  sorry

/-- The functor `Def_P ⟶ Def_{P^h}` as a morphism of categories over `C_Λ`. -/
def henselizationBasedFunctor :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor
        (deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)) where
  toFunctor := henselizationFunctor Λ k P
  w := henselizationFunctor_comp_forget Λ k P

/-- Pair henselization of a Noetherian local ring remains Noetherian. -/
instance instIsNoetherianRing_henselizationRing_maximalIdeal :
    IsNoetherianRing (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) :=
  henselizationRing_isNoetherian (pairOfIdeal (maximalIdeal P))

/-- The extended maximal ideal of a local ring in its henselization. -/
def henselExtendedMaximalIdealOf :
    Ideal (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u) :=
  Ideal.map (toHenselization (pairOfIdeal (maximalIdeal P))) (maximalIdeal P)

/-- Pair henselization followed by `henselizationToAdicCompletion` is the
canonical map into the adic completion. -/
theorem henselizationToAdicCompletion_comp_toHenselization
    (X : RingPairCat.{u}) [IsNoetherianRing X.ring] :
    (henselizationToAdicCompletion X).comp (toHenselization X) =
      algebraMap X.ring (AdicCompletion X.ideal X.ring) :=
  congrArg ringHom
    (((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
        ⟨adicCompletionPair X, adicCompletion_henselian X⟩).apply_symm_apply
      (toAdicCompletionPair X))

/-- Completing `P^h` along the extended maximal ideal is adically continuous
toward the maximal ideal of `P^∧`. -/
theorem henselizationToCompleteAdicContinuous :
    (henselizationToAdicCompletion (pairOfIdeal (maximalIdeal P))).AdicContinuous
      (henselExtendedMaximalIdealOf P)
      (maximalIdeal (AdicCompletion (maximalIdeal P) P)) :=
  ⟨1, (pow_one (henselExtendedMaximalIdealOf P)).symm ▸
    le_of_eq
      ((Ideal.map_map (toHenselization (pairOfIdeal (maximalIdeal P)))
          (henselizationToAdicCompletion (pairOfIdeal (maximalIdeal P)))).trans
        ((congrArg (fun φ ↦ Ideal.map φ (maximalIdeal P))
            (henselizationToAdicCompletion_comp_toHenselization
              (pairOfIdeal (maximalIdeal P)))).trans
          AdicCompletion.maximalIdeal_eq_map.symm))⟩

end FlatAlgebraCat

namespace FlatAlgebraCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable [henselianPairInclusion.IsRightAdjoint]
variable {Q : Type u} [CommRing Q] [Algebra k Q] [IsNoetherianRing Q]

/-- Inverse image `J_Q = f⁻¹(J)` of `J` along the structure map of a deformation of `Q`. -/
def deformationComapIdeal (J : Ideal Q) {R : FlatAlgebraCat Λ k}
    (f : R ⟶ ofResidue Λ k Q) : Ideal R.algebra :=
  Ideal.comap f.toRingHom J

/-- Completing a Noetherian deformation along `J_Q` remains flat over the Artinian base. -/
instance instModuleFlat_deformationCompletion (J : Ideal Q) {R : FlatAlgebraCat Λ k}
    (f : R ⟶ ofResidue Λ k Q) :
    Module.Flat R.base.carrier (AdicCompletion (deformationComapIdeal J f) R.algebra) :=
  sorry

/-- The completed pair `(A, R^∧)` of a deformation of `Q`. -/
def deformationCompletionObj (J : Ideal Q) {R : FlatAlgebraCat Λ k}
    (f : R ⟶ ofResidue Λ k Q) : FlatAlgebraCat Λ k :=
  of R.base (AdicCompletion (deformationComapIdeal J f) R.algebra)

/-- The structure map of a deformation of `Q` is adically continuous toward `J`. -/
theorem deformationCompletionAdicContinuous (J : Ideal Q) {R : FlatAlgebraCat Λ k}
    (f : R ⟶ ofResidue Λ k Q) :
    f.toRingHom.AdicContinuous (deformationComapIdeal J f) J :=
  ⟨1, (pow_one (deformationComapIdeal J f)).symm ▸ Ideal.map_comap_le⟩

/-- The completed residue arrow `(A, R^∧) ⟶ (k, Q^∧)`. -/
def deformationCompletionHom (J : Ideal Q) {R : FlatAlgebraCat Λ k}
    (f : R ⟶ ofResidue Λ k Q) :
    deformationCompletionObj J f ⟶ ofResidue Λ k (AdicCompletion J Q) :=
  Hom.of f.baseHom (deformationCompletionAdicContinuous J f).completionMap sorry sorry

/-- Adic continuity of a morphism of deformations of `Q` between inverse images of `J`. -/
theorem deformationCompletionMapAdicContinuous (J : Ideal Q) {ξ η : deformationCategory Λ k Q}
    (g : ξ ⟶ η) :
    g.left.toRingHom.AdicContinuous (deformationComapIdeal J ξ.hom)
      (deformationComapIdeal J η.hom) :=
  ⟨1, (pow_one (deformationComapIdeal J ξ.hom)).symm ▸
    Ideal.map_le_iff_le_comap.mpr
      ((le_of_eq (congrArg (fun h ↦ Ideal.comap h.toRingHom J) g.w).symm).trans
        (le_of_eq (Ideal.comap_comap g.left.toRingHom η.hom.toRingHom).symm))⟩

/-- The completed left arrow of a morphism of deformations of `Q`. -/
def deformationCompletionMapHom (J : Ideal Q) {ξ η : deformationCategory Λ k Q} (g : ξ ⟶ η) :
    deformationCompletionObj J ξ.hom ⟶ deformationCompletionObj J η.hom :=
  Hom.of g.left.baseHom (deformationCompletionMapAdicContinuous J g).completionMap sorry sorry

/-- The functor `Def_Q ⥤ Def_{AdicCompletion J Q}` completing deformations along `J`. -/
def deformationCompletionFunctor (J : Ideal Q) :
    deformationCategory Λ k Q ⥤ deformationCategory Λ k (AdicCompletion J Q) where
  obj ξ := Over.mk (deformationCompletionHom J ξ.hom)
  map g := Over.homMk (deformationCompletionMapHom J g) sorry
  map_id := sorry
  map_comp := sorry

variable (Λ k) in
/-- Postcompose the residue of a deformation along a bijective `k`-algebra map of
residue rings, keeping the same Artinian local base. -/
def deformationResidueTransport {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom) :
    deformationCategory Λ k R ⥤ deformationCategory Λ k S where
  obj ξ := Over.mk (ξ.hom ≫ Hom.of (𝟙 (ofResidue Λ k R).base) φ.toRingHom sorry sorry)
  map g := Over.homMk g.left sorry
  map_id := sorry
  map_comp := sorry

variable (Λ k) in
/-- Residue transport does not change the Artinian local base. -/
theorem deformationResidueTransport_obj_base {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom)
    (ξ : deformationCategory Λ k R) :
    ((deformationResidueTransport Λ k φ hφ).obj ξ).left.base = ξ.left.base :=
  sorry

end FlatAlgebraCat

namespace FlatAlgebraCat

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [henselianPairInclusion.IsRightAdjoint]

/-- The completion of `P^h` along the extended maximal ideal. -/
abbrev henselCompleteRing (P : Type u) [CommRing P] [IsLocalRing P] : Type u :=
  AdicCompletion (henselExtendedMaximalIdealOf P)
    (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)

/-- Comparison `(P^h)^∧ →ₐ[k] P^∧` induced by pair henselization. -/
def henselCompletionToComplete (k : Type u) [Field k] (P : Type u)
    [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    henselCompleteRing P →ₐ[k] AdicCompletion (maximalIdeal P) P where
  toRingHom :=
    (AdicCompletion.ofAlgEquiv
        (maximalIdeal (AdicCompletion (maximalIdeal P) P))).symm.toRingHom.comp
      (henselizationToCompleteAdicContinuous P).completionMap
  commutes' := sorry

/-- Completing the henselization recovers the completion of the local ring. -/
theorem henselCompletionToComplete_bijective (k : Type u) [Field k] (P : Type u)
    [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    Function.Bijective (henselCompletionToComplete k P).toRingHom :=
  sorry

/-- The based functor `Def_{P^h} ⥤ᵇ Def_{P^∧}` for a Noetherian local `k`-algebra,
completing along the extended maximal ideal and transporting the residue ring along
`henselizationToAdicCompletion`. -/
def completionFromHenselLocalBasedFunctor (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k] (P : Type u)
    [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P] :
    BasedCategory.ofFunctor
        (deformationForget Λ k (henselizationRing (pairOfIdeal (maximalIdeal P)) : Type u)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (AdicCompletion (maximalIdeal P) P)) where
  toFunctor :=
    Functor.comp (deformationCompletionFunctor (henselExtendedMaximalIdealOf P))
      (deformationResidueTransport Λ k (henselCompletionToComplete k P)
        (henselCompletionToComplete_bijective k P))
  w := sorry

end FlatAlgebraCat

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]
variable {ι : Type u}

/-- The slice projection `p_{x0} : Def_X ⥤ C_Λ` of Example 93.9.1. -/
abbrev deformationForget : deformationCategory Λ k X hX ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k

/-- The slice projection of `Def_X` evaluates an object `(A, Y) → (k, X)` to `A`. -/
theorem deformationForget_obj (ξ : deformationCategory Λ k X hX) :
    (deformationForget Λ k X hX).obj ξ = ξ.left.base :=
  sorry

/-- The slice projection of `Def_X` is cofibered in groupoids. -/
instance instInGroupoids_deformationForget :
    IsFibered.InGroupoids (deformationForget Λ k X hX).op :=
  sorry

/-- Stalk at each named point, as a based functor into the product of the local
deformation categories. -/
def stalkPiBasedFunctor (p : ι → X) :
    BasedCategory.ofFunctor (deformationForget Λ k X hX) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ structureStalk X hX (p i)) :=
  FlatAlgebraCat.pairing Λ k (fun i ↦ structureStalk X hX (p i))
    (deformationForget Λ k X hX) fun i ↦ stalkAlgebraBasedFunctor Λ k X hX (p i)

/-- The underlying functor of `stalkPiBasedFunctor` retains the Artinian base. -/
theorem stalkPiBasedFunctor_obj_base (p : ι → X) (ξ : deformationCategory Λ k X hX) :
    ((stalkPiBasedFunctor Λ k X hX p).toFunctor.obj ξ).1 =
      (deformationForget Λ k X hX).obj ξ :=
  sorry

/-- The `i`-th factor of `stalkPiBasedFunctor` is `stalkAlgebraBasedFunctor` at
`p i`. -/
theorem stalkPiBasedFunctor_eval (p : ι → X) (ξ : deformationCategory Λ k X hX) (i : ι) :
    (FlatAlgebraCat.evalBasedFunctor Λ k (fun j ↦ structureStalk X hX (p j)) i).toFunctor.obj
        ((stalkPiBasedFunctor Λ k X hX p).toFunctor.obj ξ) =
      (stalkAlgebraBasedFunctor Λ k X hX (p i)).toFunctor.obj ξ :=
  sorry

variable [henselianPairInclusion.IsRightAdjoint]

/-- Pair henselization of each local stalk, as a based functor of deformation
products. -/
def henselizationPiBasedFunctor [IsLocallyNoetherian X] (p : ι → X) :
    BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ structureStalk X hX (p i)) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ henselStalk X hX (p i)) :=
  FlatAlgebraCat.deformationPiMap Λ k (fun i ↦ structureStalk X hX (p i))
    (fun i ↦ henselStalk X hX (p i)) fun i ↦
      FlatAlgebraCat.henselizationBasedFunctor Λ k (structureStalk X hX (p i))

/-- The underlying functor of `henselizationPiBasedFunctor` retains the Artinian
base. -/
theorem henselizationPiBasedFunctor_obj_base [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ structureStalk X hX (p i)) :
    ((henselizationPiBasedFunctor Λ k X hX p).toFunctor.obj x).1 = x.1 :=
  sorry

/-- The `i`-th factor of `henselizationPiBasedFunctor` is pair henselization of
`structureStalk` along its maximal ideal. -/
theorem henselizationPiBasedFunctor_eval [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ structureStalk X hX (p i)) (i : ι) :
    (FlatAlgebraCat.evalBasedFunctor Λ k (fun j ↦ henselStalk X hX (p j)) i).toFunctor.obj
        ((henselizationPiBasedFunctor Λ k X hX p).toFunctor.obj x) =
      (FlatAlgebraCat.henselizationBasedFunctor Λ k (structureStalk X hX (p i))).toFunctor.obj
        (Fiber.fiberInclusion.obj (x.2 i)) :=
  sorry

/-- Adic completion of each henselian local stalk, as a based functor of
deformation products landing in `∏ Def_{O_{X, p i}^∧}`. -/
def completionPiBasedFunctor [IsLocallyNoetherian X] (p : ι → X) :
    BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ henselStalk X hX (p i)) ⥤ᵇ
      BasedCategory.ofFunctor
        (FlatAlgebraCat.deformationPiForget Λ k fun i ↦ completeStalk X hX (p i)) :=
  FlatAlgebraCat.deformationPiMap Λ k (fun i ↦ henselStalk X hX (p i))
    (fun i ↦ completeStalk X hX (p i)) fun i ↦
      FlatAlgebraCat.completionFromHenselLocalBasedFunctor Λ k (structureStalk X hX (p i))

/-- The underlying functor of `completionPiBasedFunctor` retains the Artinian base. -/
theorem completionPiBasedFunctor_obj_base [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ henselStalk X hX (p i)) :
    ((completionPiBasedFunctor Λ k X hX p).toFunctor.obj x).1 = x.1 :=
  sorry

/-- The `i`-th factor of `completionPiBasedFunctor` is the henselization-to-completion
transport `completionFromHenselLocalBasedFunctor`. -/
theorem completionPiBasedFunctor_eval [IsLocallyNoetherian X] (p : ι → X)
    (x : FlatAlgebraCat.deformationPi Λ k fun i ↦ henselStalk X hX (p i)) (i : ι) :
    (FlatAlgebraCat.evalBasedFunctor Λ k (fun j ↦ completeStalk X hX (p j)) i).toFunctor.obj
        ((completionPiBasedFunctor Λ k X hX p).toFunctor.obj x) =
      (FlatAlgebraCat.completionFromHenselLocalBasedFunctor Λ k
          (structureStalk X hX (p i))).toFunctor.obj
        (Fiber.fiberInclusion.obj (x.2 i)) :=
  sorry

end FlatSchemeCat

end

