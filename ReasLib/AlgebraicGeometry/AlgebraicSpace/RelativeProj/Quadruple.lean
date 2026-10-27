/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Triple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative

/-!
# Relative projective quadruples over algebraic spaces

A test object of the relative projective functor is a quadruple `(d, f, ℒ, ψ)` consisting
of a positive Veronese degree, a morphism to the base algebraic space, an invertible
module, and a graded algebra map inducing a surjection `f^* 𝒜_d ⟶ ℒ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The unlifted degree-zero unit of `deg` is the algebra unit of `𝒜`, transported
along `deg.iso 0`. -/
theorem degreeZeroUnit_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)} (deg : DegreePieces 𝒜) :
    Modules.liftModuleMap (degreeZeroUnit deg) =
      (Modules.liftedUnitIso X).hom ≫ gradedOneHom 𝒜 ≫ (deg.iso 0).inv :=
  sorry

/-- The index identity `m * n = m * a * d` when `n = a * d`. -/
private theorem commonMultiple_index (m n a d : ℕ) (hn : n = a * d) : m * n = m * a * d :=
  (congrArg (fun k ↦ m * k) hn).trans (Nat.mul_assoc m a d).symm

/-- The index identity `(m + 1) * a = a + m * a`. -/
private theorem succ_mul_eq_add (m a : ℕ) : (m + 1) * a = a + m * a :=
  (Nat.succ_mul m a).trans (Nat.add_comm (m * a) a)

/-- Reassociation of unit-based tensor powers `(ℒ^{⊗ (m * a)}) ≅ (ℒ^{⊗ a})^{⊗ m}`. -/
def tensorPowerUnitMulIso {Y : AlgebraicSpace S} (L : Y.Modules) (a : ℕ) :
    (m : ℕ) → tensorPowerUnit L (m * a) ≅ tensorPowerUnit (tensorPowerUnit L a) m :=
  Nat.rec
    (eqToIso (congrArg (tensorPowerUnit L) (Nat.zero_mul a)) ≪≫
      eqToIso (tensorPowerUnit_zero L) ≪≫
        (eqToIso (tensorPowerUnit_zero (tensorPowerUnit L a))).symm)
    (fun m rec ↦
      eqToIso (congrArg (tensorPowerUnit L) (by exact succ_mul_eq_add m a)) ≪≫
        (tensorPowerUnitAddIso L a (m * a)).symm ≪≫
          (Iso.refl (tensorPowerUnit L a) ⊗ᵢ rec) ≪≫
            eqToIso (tensorPowerUnit_succ (tensorPowerUnit L a) m).symm)

/-- A relative projective quadruple over a test scheme. -/
structure Quadruple
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜) (T : Over S) where
  /-- The positive Veronese degree `d`. -/
  degree : ℕ
  /-- Positivity of the Veronese degree. -/
  positive : 1 ≤ degree
  /-- The structure morphism `f : T ⟶ X` over `S`, as a morphism of algebraic spaces. -/
  morphism : ofOver T ⟶ X
  /-- The invertible `𝒪_T`-module. -/
  lineBundle : (ofOver T).Modules
  /-- Invertibility of the chosen module. -/
  lineBundle_invertible : isInvertibleObject lineBundle
  /-- Degreewise components of `ψ : f^* 𝒜^{(d)} ⟶ ⊕_{n ≥ 0} ℒ^{⊗ n}` on the pullback side. -/
  psi : ∀ n : ℕ,
    (Modules.pullback morphism).obj (deg.obj (n * degree)) ⟶ tensorPowerUnit lineBundle n
  /-- The degree-zero map sends the pulled-back unit of `𝒜` to the tensor-power unit. -/
  psi_map_one :
    Modules.structureModulePullbackInv morphism ≫
        (Modules.pullback morphism).map (degreeZeroUnit deg) ≫
          eqToHom
              (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                (Nat.zero_mul degree).symm) ≫
            psi 0 =
      eqToHom (tensorPowerUnit_zero lineBundle).symm
  /-- The degreewise map preserves multiplication of Veronese-homogeneous pieces. -/
  psi_map_mul :
    ∀ i j : ℕ,
      pullbackTensorLax morphism (deg.obj (i * degree)) (deg.obj (j * degree)) ≫
          (Modules.pullback morphism).map (deg.mul (i * degree) (j * degree)) ≫
            eqToHom
                (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                  (Nat.add_mul i j degree).symm) ≫
              psi (i + j) =
        tensorHom (psi i) (psi j) ≫ (tensorPowerUnitAddIso lineBundle i j).hom
  /-- The pullback-side degree-one map `f^* 𝒜_d ⟶ ℒ`. -/
  degreeOneMap :
    (Modules.pullback morphism).obj (deg.obj (1 * degree)) ⟶ tensorPowerUnit lineBundle 1
  /-- The displayed degree-one map is the degree-one component of `ψ`. -/
  degreeOneMap_spec : degreeOneMap = psi 1
  /-- The degree-one map is an epimorphism. -/
  degreeOne_surjective : Epi degreeOneMap

namespace Quadruple

/-- Construct a relative projective quadruple from its positive degree, structure
morphism, invertible module, and multiplicative homogeneous maps with an epimorphic
degree-one component. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (degree : ℕ) (positive : 1 ≤ degree) (morphism : ofOver T ⟶ X)
    (lineBundle : (ofOver T).Modules) (lineBundle_invertible : isInvertibleObject lineBundle)
    (psi : ∀ n : ℕ,
      (Modules.pullback morphism).obj (deg.obj (n * degree)) ⟶ tensorPowerUnit lineBundle n)
    (psi_map_one :
      Modules.structureModulePullbackInv morphism ≫
          (Modules.pullback morphism).map (degreeZeroUnit deg) ≫
            eqToHom
              (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                (Nat.zero_mul degree).symm) ≫
              psi 0 =
        eqToHom (tensorPowerUnit_zero lineBundle).symm)
    (psi_map_mul : ∀ i j : ℕ,
      pullbackTensorLax morphism (deg.obj (i * degree)) (deg.obj (j * degree)) ≫
          (Modules.pullback morphism).map (deg.mul (i * degree) (j * degree)) ≫
            eqToHom
              (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                (Nat.add_mul i j degree).symm) ≫
              psi (i + j) =
        tensorHom (psi i) (psi j) ≫ (tensorPowerUnitAddIso lineBundle i j).hom)
    (degreeOneMap :
      (Modules.pullback morphism).obj (deg.obj (1 * degree)) ⟶ tensorPowerUnit lineBundle 1)
    (degreeOneMap_spec : degreeOneMap = psi 1) (degreeOne_surjective : Epi degreeOneMap) :
    Quadruple 𝒜 deg T where
  degree := degree
  positive := positive
  morphism := morphism
  lineBundle := lineBundle
  lineBundle_invertible := lineBundle_invertible
  psi := psi
  psi_map_one := psi_map_one
  psi_map_mul := psi_map_mul
  degreeOneMap := degreeOneMap
  degreeOneMap_spec := degreeOneMap_spec
  degreeOne_surjective := degreeOne_surjective

/-- The positivity, invertibility, degree-one identification, and epimorphism conditions
hold simultaneously. -/
theorem conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : Quadruple 𝒜 deg T) :
    1 ≤ q.degree ∧
      isInvertibleObject q.lineBundle ∧
      q.degreeOneMap = q.psi 1 ∧
      Epi q.degreeOneMap :=
  sorry

/-- Restrict one homogeneous component of a quadruple to a specified common multiple and
rebracket its target as a tensor power of the powered line bundle. -/
def commonMultipleDegreeMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : Quadruple 𝒜 deg T) (n a : ℕ)
    (hn : n = a * q.degree) (m : ℕ) :
    (Modules.pullback q.morphism).obj (deg.obj (m * n)) ⟶
      tensorPowerUnit (tensorPowerUnit q.lineBundle a) m :=
  eqToHom
      (congrArg (fun k ↦ (Modules.pullback q.morphism).obj (deg.obj k))
        (by exact commonMultiple_index m n a q.degree hn)) ≫
    q.psi (m * a) ≫ (tensorPowerUnitMulIso q.lineBundle a m).hom

/-- Two quadruples are compatible at a specified common multiple when their structure
morphisms agree and an isomorphism of the powered line bundles identifies every
restricted homogeneous map. -/
def CompatibleAt {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (q q' : Quadruple 𝒜 deg T) (n a a' : ℕ)
    (hn : n = a * q.degree) (hn' : n = a' * q'.degree) : Prop :=
  q.morphism = q'.morphism ∧
    ∃ beta : tensorPowerUnit q.lineBundle a ≅ tensorPowerUnit q'.lineBundle a',
      ∀ m : ℕ,
        HEq
          (commonMultipleDegreeMap q n a hn m ≫ tensorPowerUnitMap beta.hom m)
          (commonMultipleDegreeMap q' n a' hn' m)

/-- Two quadruples are equivalent when they are compatible at the product of their
positive degrees. -/
def Equivalent {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q q' : Quadruple 𝒜 deg T) : Prop :=
  CompatibleAt q q' (q.degree * q'.degree) q'.degree q.degree
    (Nat.mul_comm q.degree q'.degree) rfl

/-- Equivalence is compatibility at the product of the two positive Veronese degrees. -/
theorem equivalent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q q' : Quadruple 𝒜 deg T) :
    Equivalent q q' ↔
      CompatibleAt q q' (q.degree * q'.degree) q'.degree q.degree
        (Nat.mul_comm q.degree q'.degree) rfl :=
  Iff.rfl

/-- Equivalence of quadruples is compatibility at some positive common multiple of their degrees. -/
theorem equivalent_iff_exists_commonMultiple {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q q' : Quadruple 𝒜 deg T) :
    Equivalent q q' ↔ ∃ n a a' : ℕ, 1 ≤ n ∧
      ∃ (hn : n = a * q.degree) (hn' : n = a' * q'.degree),
        q.morphism = q'.morphism ∧
          ∃ beta : tensorPowerUnit q.lineBundle a ≅ tensorPowerUnit q'.lineBundle a',
            ∀ m : ℕ, HEq
              (commonMultipleDegreeMap q n a hn m ≫ tensorPowerUnitMap beta.hom m)
              (commonMultipleDegreeMap q' n a' hn' m) := sorry

/-- The structure morphism of the pullback of a quadruple along a morphism of test schemes. -/
def pullbackMorphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) : ofOver T' ⟶ X :=
  ofOverMap g ≫ q.morphism

/-- The line bundle of the pullback of a quadruple is the module pullback of the original
line bundle. -/
def pullbackLineBundle {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) : (ofOver T').Modules :=
  (Modules.pullback (ofOverMap g)).obj q.lineBundle

/-- Homogeneous components of the pullback of a quadruple. -/
def pullbackPsi {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) (n : ℕ) :
    (Modules.pullback (pullbackMorphism g q)).obj (deg.obj (n * q.degree)) ⟶
      tensorPowerUnit (pullbackLineBundle g q) n :=
  ((AlgebraicGeometry.AlgebraicSpace.Modules.pullbackCompIso
        (ofOverMap g) q.morphism).inv.app (deg.obj (n * q.degree))) ≫
    (Modules.pullback (ofOverMap g)).map (q.psi n) ≫
      pullbackTensorPowerHom (ofOverMap g) q.lineBundle n

/-- The pullback-side degree-one map of a pulled-back quadruple. -/
def pullbackDegreeOneMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) :
    (Modules.pullback (pullbackMorphism g q)).obj (deg.obj (1 * q.degree)) ⟶
      tensorPowerUnit (pullbackLineBundle g q) 1 :=
  pullbackPsi g q 1

/-- Pull back a relative projective quadruple along a morphism of test schemes. -/
def pullback {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) : Quadruple 𝒜 deg T' := by
  let degree := q.degree
  let positive := q.positive
  let morphism := pullbackMorphism g q
  let lineBundle := pullbackLineBundle g q
  let psi := pullbackPsi g q
  let degreeOneMap := pullbackDegreeOneMap g q
  have laws :
    (isInvertibleObject lineBundle) ∧
    (Modules.structureModulePullbackInv morphism ≫
        (Modules.pullback morphism).map (degreeZeroUnit deg) ≫
          eqToHom
              (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                (Nat.zero_mul degree).symm) ≫
            psi 0 =
      eqToHom (tensorPowerUnit_zero lineBundle).symm) ∧
    (∀ i j : ℕ,
      pullbackTensorLax morphism (deg.obj (i * degree)) (deg.obj (j * degree)) ≫
          (Modules.pullback morphism).map (deg.mul (i * degree) (j * degree)) ≫
            eqToHom
                (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                  (Nat.add_mul i j degree).symm) ≫
              psi (i + j) =
        tensorHom (psi i) (psi j) ≫ (tensorPowerUnitAddIso lineBundle i j).hom) ∧
    (degreeOneMap = psi 1) ∧
    (Epi degreeOneMap) := by sorry
  exact {
    degree := degree
    positive := positive
    morphism := morphism
    lineBundle := lineBundle
    psi := psi
    degreeOneMap := degreeOneMap
    lineBundle_invertible := laws.1
    psi_map_one := laws.2.1
    psi_map_mul := laws.2.2.1
    degreeOneMap_spec := laws.2.2.2.1
    degreeOne_surjective := laws.2.2.2.2 }

/-- The structure morphism of `pullback g q` is `ofOverMap g ≫ q.morphism`. -/
theorem pullback_morphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) :
    (pullback g q).morphism = ofOverMap g ≫ q.morphism :=
  rfl

/-- The line bundle of `pullback g q` is the module pullback of `q.lineBundle`. -/
theorem pullback_lineBundle {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) :
    (pullback g q).lineBundle = (Modules.pullback (ofOverMap g)).obj q.lineBundle :=
  rfl

/-- Pullback preserves the Veronese degree. -/
theorem pullback_degree {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : Quadruple 𝒜 deg T) :
    (pullback g q).degree = q.degree :=
  rfl

/-- The structure morphism of a quadruple pushed along `g : Z ⟶ X` is `t ≫ g`. -/
def pushalongMorphism {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    (g : ofOver Z ⟶ X) {T : Over S} (t : ofOver T ⟶ ofOver Z) :
    ofOver T ⟶ X :=
  t ≫ g

/-- `pushalongMorphism g t` is the composite `t ≫ g`. -/
theorem pushalongMorphism_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    (g : ofOver Z ⟶ X) {T : Over S} (t : ofOver T ⟶ ofOver Z) :
    pushalongMorphism g t = t ≫ g :=
  rfl

/-- Homogeneous components of a quadruple after rewriting its structure morphism as `t ≫ g`. -/
def pushalongPsi {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (t : ofOver T ⟶ ofOver Z)
    (g : ofOver Z ⟶ X) (q : Quadruple 𝒜 deg T)
    (h : q.morphism = t ≫ g) (n : ℕ) :
    (Modules.pullback (pushalongMorphism g t)).obj (deg.obj (n * q.degree)) ⟶
      tensorPowerUnit q.lineBundle n :=
  eqToHom
      (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj (n * q.degree))) h.symm) ≫
    q.psi n

/-- Push a quadruple along `g : Z ⟶ X` by viewing a quadruple whose structure morphism
already factors as `t ≫ g` as the image of `(d, t, L, ψ) ↦ (d, g ∘ t, L, ψ)`. -/
def pushalong {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (t : ofOver T ⟶ ofOver Z)
    (g : ofOver Z ⟶ X) (q : Quadruple 𝒜 deg T)
    (h : q.morphism = t ≫ g) : Quadruple 𝒜 deg T := by
  let degree := q.degree
  let positive := q.positive
  let morphism := pushalongMorphism g t
  let lineBundle := q.lineBundle
  let psi := pushalongPsi t g q h
  let degreeOneMap := pushalongPsi t g q h 1
  have laws :
    (isInvertibleObject lineBundle) ∧
    (Modules.structureModulePullbackInv morphism ≫
        (Modules.pullback morphism).map (degreeZeroUnit deg) ≫
          eqToHom
              (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                (Nat.zero_mul degree).symm) ≫
            psi 0 =
      eqToHom (tensorPowerUnit_zero lineBundle).symm) ∧
    (∀ i j : ℕ,
      pullbackTensorLax morphism (deg.obj (i * degree)) (deg.obj (j * degree)) ≫
          (Modules.pullback morphism).map (deg.mul (i * degree) (j * degree)) ≫
            eqToHom
                (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                  (Nat.add_mul i j degree).symm) ≫
              psi (i + j) =
        tensorHom (psi i) (psi j) ≫ (tensorPowerUnitAddIso lineBundle i j).hom) ∧
    (degreeOneMap = psi 1) ∧
    (Epi degreeOneMap) := by sorry
  exact {
    degree := degree
    positive := positive
    morphism := morphism
    lineBundle := lineBundle
    psi := psi
    degreeOneMap := degreeOneMap
    lineBundle_invertible := laws.1
    psi_map_one := laws.2.1
    psi_map_mul := laws.2.2.1
    degreeOneMap_spec := laws.2.2.2.1
    degreeOne_surjective := laws.2.2.2.2 }

/-- The structure morphism of `pushalong t g q h` is `t ≫ g`. -/
theorem pushalong_morphism {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (t : ofOver T ⟶ ofOver Z)
    (g : ofOver Z ⟶ X) (q : Quadruple 𝒜 deg T)
    (h : q.morphism = t ≫ g) :
    (pushalong t g q h).morphism = t ≫ g :=
  rfl

/-- Pushalong preserves the Veronese degree. -/
theorem pushalong_degree {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (t : ofOver T ⟶ ofOver Z)
    (g : ofOver Z ⟶ X) (q : Quadruple 𝒜 deg T)
    (h : q.morphism = t ≫ g) :
    (pushalong t g q h).degree = q.degree :=
  rfl

/-- Pushalong preserves the line bundle. -/
theorem pushalong_lineBundle {S : Scheme.{u}} {X : AlgebraicSpace S} {Z : Over S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (t : ofOver T ⟶ ofOver Z)
    (g : ofOver Z ⟶ X) (q : Quadruple 𝒜 deg T)
    (h : q.morphism = t ≫ g) :
    (pushalong t g q h).lineBundle = q.lineBundle :=
  rfl

end Quadruple


end AlgebraicGeometry.AlgebraicSpace.RelativeProj

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.DegreePieces

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

/-- The supplied degree presentation inherits the original algebra's QCoh property. -/
theorem isQuasicoherent (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) (n : ℕ) :
    (deg.obj n).IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.DegreePieces
