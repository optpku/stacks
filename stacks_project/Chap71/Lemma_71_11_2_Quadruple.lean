/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Lemma_71_11_11_Triple

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

/-- The index identity `(i + j) * d = i * d + j * d` used to compare Veronese pieces. -/
theorem veronese_add (i j d : ℕ) : (i + j) * d = i * d + j * d :=
  Nat.add_mul i j d

/-- The index identity `m * n = m * a * d` when `n = a * d`. -/
theorem commonMultiple_index (m n a d : ℕ) (hn : n = a * d) : m * n = m * a * d :=
  (congrArg (fun k ↦ m * k) hn).trans (Nat.mul_assoc m a d).symm

/-- The index identity `(m + 1) * a = a + m * a`. -/
theorem succ_mul_eq_add (m a : ℕ) : (m + 1) * a = a + m * a :=
  (Nat.succ_mul m a).trans (Nat.add_comm (m * a) a)

/-- Reassociation of unit-based tensor powers `(ℒ^{⊗ (m * a)}) ≅ (ℒ^{⊗ a})^{⊗ m}`. -/
def tensorPowerUnitMulIso {Y : AlgebraicSpace S} (L : Y.Modules) (a : ℕ) :
    (m : ℕ) → tensorPowerUnit L (m * a) ≅ tensorPowerUnit (tensorPowerUnit L a) m :=
  Nat.rec
    (eqToIso (congrArg (tensorPowerUnit L) (Nat.zero_mul a)) ≪≫
      eqToIso (tensorPowerUnit_zero L) ≪≫
        (eqToIso (tensorPowerUnit_zero (tensorPowerUnit L a))).symm)
    (fun m rec ↦
      eqToIso (congrArg (tensorPowerUnit L) (succ_mul_eq_add m a)) ≪≫
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
                  (veronese_add i j degree).symm) ≫
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

/-- Construct a relative projective quadruple from a positive degree, morphism, invertible
module, graded map, unit and multiplication laws, and the pullback-side degree-one
epimorphism. -/
abbrev of := @Quadruple.mk

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
        (commonMultiple_index m n a q.degree hn)) ≫
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
  sorry

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
    (q : Quadruple 𝒜 deg T) : Quadruple 𝒜 deg T' :=
  of q.degree q.positive (pullbackMorphism g q) (pullbackLineBundle g q) sorry
    (pullbackPsi g q) sorry sorry (pullbackDegreeOneMap g q) sorry sorry

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
    (h : q.morphism = t ≫ g) : Quadruple 𝒜 deg T :=
  of q.degree q.positive (pushalongMorphism g t) q.lineBundle q.lineBundle_invertible
    (pushalongPsi t g q h) sorry sorry
    (pushalongPsi t g q h 1) sorry sorry

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


/-- A size-safe relative projective functor over the functor of points of an algebraic space. -/
structure ProjFunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) where
  /-- The functor on schemes over `S` underlying `F`. -/
  toFunctor : (Over S)ᵒᵖ ⥤ Type u
  /-- The structural map to the functor of points of the base algebraic space. -/
  baseMap : toFunctor ⟶ X.functorOfPoints
  /-- Every graded piece of the underlying algebra sheaf is quasicoherent. -/
  algebra_isQuasicoherent : 𝒜.IsQuasicoherent
  /-- Ordinary commutativity from the source's ring convention (algebra.tex:37). -/
  algebra_isCommutative : 𝒜.IsCommutative

/-- Construct a relative projective functor from a functor over `X.functorOfPoints` and
quasicoherence of `𝒜`. -/
def ProjFunctor.ofFunctor {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (toFunctor : (Over S)ᵒᵖ ⥤ Type u) (baseMap : toFunctor ⟶ X.functorOfPoints)
    (algebra_isQuasicoherent : 𝒜.IsQuasicoherent)
    (algebra_isCommutative : 𝒜.IsCommutative) :
    ProjFunctor X 𝒜 where
  toFunctor := toFunctor
  baseMap := baseMap
  algebra_isQuasicoherent := algebra_isQuasicoherent
  algebra_isCommutative := algebra_isCommutative

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
