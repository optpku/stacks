module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree-`n` piece of a graded algebra sheaf on the universe-lifted commutative small
étale site of an algebraic space. -/
abbrev degreeModule (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (n : ℕ) : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  𝒜.obj (Int.ofNat n)

/-- `degreeModule 𝒜 n` is the degree-`n` summand of `𝒜`. -/
theorem degreeModule_eq (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (n : ℕ) : degreeModule 𝒜 n = 𝒜.obj (Int.ofNat n) :=
  rfl

/-- Unlifted homogeneous pieces of a graded algebra sheaf, identified with the universe-lifted
components after `liftModule`, together with the unlifted multiplication of homogeneous
pieces. -/
structure DegreePieces {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) where
  /-- The unlifted degree-`n` piece as an `𝒪_X`-module. -/
  obj : ℕ → X.Modules
  /-- Universe lift recovers the homogeneous component of `𝒜`. -/
  iso : ∀ n : ℕ, Modules.liftModule (obj n) ≅ degreeModule 𝒜 n
  /-- Unlifted multiplication of homogeneous pieces. -/
  mul : ∀ i j : ℕ, obj i ⊗ obj j ⟶ obj (i + j)
  /-- Unlifted multiplication is the transport of `GradedAlgebraSheaf.mulHom` along `iso`. -/
  mul_spec : ∀ i j : ℕ,
    liftModuleTensorHom (obj i) (obj j) ≫ Modules.liftModuleMap (mul i j) =
      ((iso i).hom ⊗ₘ (iso j).hom) ≫
        GradedAlgebraSheaf.mulHom 𝒜 (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg 𝒜.obj (Int.natCast_add i j).symm) ≫
            (iso (i + j)).inv

namespace DegreePieces

/-- Construct unlifted degree pieces from a family of modules, comparison isomorphisms, and
homogeneous multiplication. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (obj : ℕ → X.Modules)
    (iso : ∀ n : ℕ, Modules.liftModule (obj n) ≅ degreeModule 𝒜 n)
    (mul : ∀ i j : ℕ, obj i ⊗ obj j ⟶ obj (i + j))
    (mul_spec : ∀ i j : ℕ,
      liftModuleTensorHom (obj i) (obj j) ≫ Modules.liftModuleMap (mul i j) =
        ((iso i).hom ⊗ₘ (iso j).hom) ≫
          GradedAlgebraSheaf.mulHom 𝒜 (Int.ofNat i) (Int.ofNat j) ≫
            eqToHom (congrArg 𝒜.obj (Int.natCast_add i j).symm) ≫
              (iso (i + j)).inv) :
    DegreePieces 𝒜 where
  obj := obj
  iso := iso
  mul := mul
  mul_spec := mul_spec

end DegreePieces

/-- The degree-zero unit morphism of a graded algebra sheaf. -/
def gradedOneHom (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    unitModule (smallEtaleTopology X) (commStructureSheafLift X) ⟶ degreeModule 𝒜 0 where
  val :=
    { app := fun U ↦
        ModuleCat.ofHom
          { toFun := fun r ↦ r • 𝒜.one U
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- The unlifted degree-zero unit of a graded algebra sheaf. -/
def degreeZeroUnit {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) :
    SheafOfModules.unit (structureSheaf X) ⟶ deg.obj 0 :=
  Modules.unliftModuleHom
    ((Modules.liftedUnitIso X).hom ≫ gradedOneHom 𝒜 ≫ (deg.iso 0).inv)

/-- Pullback of the degree-zero unit along `f`, as a section of the universe-lifted
pullback of `𝒜_0`. -/
def psiSourceOneSection {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (U : (smallEtaleSite Y)ᵒᵖ) :
    (Modules.liftModule ((Modules.pullback f).obj (deg.obj 0))).val.obj U :=
  ((Modules.liftModuleMap
        (Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map (degreeZeroUnit deg))).val.app U).hom
    (((Modules.liftedUnitIso Y).inv.val.app U).hom (liftedUnitSection Y U))

/-- The pullback-side source of a homogeneous component of `ψ`. -/
abbrev psiSource {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (n : ℕ) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift Y) :=
  Modules.liftModule ((Modules.pullback f).obj (deg.obj n))

/-- Source multiplication of pulled-back homogeneous sections, using the unlifted
multiplication of `deg` after the lift laxator and the pullback laxator. -/
def psiSourceMulHom {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    tensorObj (psiSource f deg i) (psiSource f deg j) ⟶ psiSource f deg (i + j) :=
  liftModuleTensorHom
      ((Modules.pullback f).obj (deg.obj i))
      ((Modules.pullback f).obj (deg.obj j)) ≫
    Modules.liftModuleMap
      (pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
        (Modules.pullback f).map (deg.mul i j))

/-- The product of two pulled-back homogeneous sections of `𝒜`. -/
def psiSourceMulSection {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (U : (smallEtaleSite Y)ᵒᵖ) (i j : ℕ)
    (x : (psiSource f deg i).val.obj U) (y : (psiSource f deg j).val.obj U) :
    (psiSource f deg (i + j)).val.obj U :=
  ((Modules.liftModuleMap
        (pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
          (Modules.pullback f).map (deg.mul i j))).val.app U).hom
    (liftModuleTensorSection
      ((Modules.pullback f).obj (deg.obj i))
      ((Modules.pullback f).obj (deg.obj j)) U x y)

/-- Lifted multiplication of homogeneous pieces of `𝒜` recovers `mulHom` after the stored
degreewise identifications. -/
theorem degreeMul_spec {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    liftModuleTensorHom (deg.obj i) (deg.obj j) ≫ Modules.liftModuleMap (deg.mul i j) =
      ((deg.iso i).hom ⊗ₘ (deg.iso j).hom) ≫
        GradedAlgebraSheaf.mulHom 𝒜 (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg 𝒜.obj (Int.natCast_add i j).symm) ≫
            (deg.iso (i + j)).inv :=
  sorry

/-- A degree-one relative projective triple over a test scheme `T` over `S`. -/
structure DegreeOneTriple
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜) (T : Over S) where
  /-- The structure morphism `f : T ⟶ X` over `S`, as a morphism of algebraic spaces. -/
  morphism : ofOver T ⟶ X
  /-- The invertible `𝒪_T`-module. -/
  lineBundle : (ofOver T).Modules
  /-- Invertibility of the chosen module. -/
  lineBundle_invertible : isInvertibleObject lineBundle
  /-- Degreewise components of `ψ : f^* 𝒜 ⟶ ⊕_{n ≥ 0} ℒ^{⊗ n}` on the pullback side. -/
  psi : ∀ n : ℕ,
    (Modules.pullback morphism).obj (deg.obj n) ⟶ tensorPowerUnit lineBundle n
  /-- The degreewise map sends the pulled-back unit of `𝒜` to the tensor-power unit. -/
  psi_map_one :
    ∀ U : smallEtaleSite (ofOver T),
      (((Modules.liftModuleMap (psi 0)).val.app (op U)).hom)
          (psiSourceOneSection morphism deg (op U)) =
        ((Modules.liftedUnitIso (ofOver T)).hom.val.app (op U)).hom
          (TensorPower.oneSection (commStructureSheafLift (ofOver T))
            (Modules.liftModule lineBundle) (op U))
  /-- The degreewise map preserves multiplication of homogeneous sections against
  `TensorPower.mulSection`. -/
  psi_map_mul :
    ∀ (U : smallEtaleSite (ofOver T)) (i j : ℕ)
      (x : (psiSource morphism deg i).val.obj (op U))
      (y : (psiSource morphism deg j).val.obj (op U)),
      (((Modules.liftModuleMap (psi (i + j))).val.app (op U)).hom)
          (psiSourceMulSection morphism deg (op U) i j x y) =
        ((Modules.liftModuleMap
            (tensorPowerUnitAddIso lineBundle i j).hom).val.app (op U)).hom
          (liftModuleTensorSection
            (tensorPowerUnit lineBundle i)
            (tensorPowerUnit lineBundle j) (op U)
            (((Modules.liftModuleMap (psi i)).val.app (op U)).hom x)
            (((Modules.liftModuleMap (psi j)).val.app (op U)).hom y))
  /-- The pullback-side degree-one map. -/
  degreeOneMap :
    (Modules.pullback morphism).obj (deg.obj 1) ⟶ tensorPowerUnit lineBundle 1
  /-- The displayed degree-one map is the degree-one component of `ψ`. -/
  degreeOneMap_spec : degreeOneMap = psi 1
  /-- The degree-one map is an epimorphism. -/
  degreeOne_surjective : Epi degreeOneMap

namespace DegreeOneTriple

/-- Construct a degree-one triple from a morphism, invertible module, graded map, unit and
multiplication laws, and the pullback-side degree-one epimorphism. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (morphism : ofOver T ⟶ X) (lineBundle : (ofOver T).Modules)
    (lineBundle_invertible : isInvertibleObject lineBundle)
    (psi : ∀ n : ℕ,
      (Modules.pullback morphism).obj (deg.obj n) ⟶ tensorPowerUnit lineBundle n)
    (psi_map_one :
      ∀ U : smallEtaleSite (ofOver T),
        (((Modules.liftModuleMap (psi 0)).val.app (op U)).hom)
            (psiSourceOneSection morphism deg (op U)) =
          ((Modules.liftedUnitIso (ofOver T)).hom.val.app (op U)).hom
            (TensorPower.oneSection (commStructureSheafLift (ofOver T))
              (Modules.liftModule lineBundle) (op U)))
    (psi_map_mul :
      ∀ (U : smallEtaleSite (ofOver T)) (i j : ℕ)
        (x : (psiSource morphism deg i).val.obj (op U))
        (y : (psiSource morphism deg j).val.obj (op U)),
        (((Modules.liftModuleMap (psi (i + j))).val.app (op U)).hom)
            (psiSourceMulSection morphism deg (op U) i j x y) =
          ((Modules.liftModuleMap
              (tensorPowerUnitAddIso lineBundle i j).hom).val.app (op U)).hom
            (liftModuleTensorSection
              (tensorPowerUnit lineBundle i)
              (tensorPowerUnit lineBundle j) (op U)
              (((Modules.liftModuleMap (psi i)).val.app (op U)).hom x)
              (((Modules.liftModuleMap (psi j)).val.app (op U)).hom y)))
    (degreeOneMap :
      (Modules.pullback morphism).obj (deg.obj 1) ⟶ tensorPowerUnit lineBundle 1)
    (degreeOneMap_spec : degreeOneMap = psi 1)
    (degreeOne_surjective : Epi degreeOneMap) :
    DegreeOneTriple 𝒜 deg T where
  morphism := morphism
  lineBundle := lineBundle
  lineBundle_invertible := lineBundle_invertible
  psi := psi
  psi_map_one := psi_map_one
  psi_map_mul := psi_map_mul
  degreeOneMap := degreeOneMap
  degreeOneMap_spec := degreeOneMap_spec
  degreeOne_surjective := degreeOne_surjective

/-- The invertibility, unit, multiplication, and degree-one epimorphism conditions hold
simultaneously. -/
theorem conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    isInvertibleObject q.lineBundle ∧
      (∀ U : smallEtaleSite (ofOver T),
        (((Modules.liftModuleMap (q.psi 0)).val.app (op U)).hom)
            (psiSourceOneSection q.morphism deg (op U)) =
          ((Modules.liftedUnitIso (ofOver T)).hom.val.app (op U)).hom
            (TensorPower.oneSection (commStructureSheafLift (ofOver T))
              (Modules.liftModule q.lineBundle) (op U))) ∧
      (∀ (U : smallEtaleSite (ofOver T)) (i j : ℕ)
        (x : (psiSource q.morphism deg i).val.obj (op U))
        (y : (psiSource q.morphism deg j).val.obj (op U)),
        (((Modules.liftModuleMap (q.psi (i + j))).val.app (op U)).hom)
            (psiSourceMulSection q.morphism deg (op U) i j x y) =
          ((Modules.liftModuleMap
              (tensorPowerUnitAddIso q.lineBundle i j).hom).val.app (op U)).hom
            (liftModuleTensorSection
              (tensorPowerUnit q.lineBundle i)
              (tensorPowerUnit q.lineBundle j) (op U)
              (((Modules.liftModuleMap (q.psi i)).val.app (op U)).hom x)
              (((Modules.liftModuleMap (q.psi j)).val.app (op U)).hom y))) ∧
      (q.degreeOneMap = q.psi 1) ∧
      Epi q.degreeOneMap :=
  sorry

/-- The pullback-side degree-one map of a triple. -/
def degreeMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    (Modules.pullback q.morphism).obj (deg.obj 1) ⟶ tensorPowerUnit q.lineBundle 1 :=
  q.degreeOneMap

/-- `degreeMap q` is `q.degreeOneMap`. -/
theorem degreeMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    degreeMap q = q.degreeOneMap :=
  rfl

/-- `degreeOneMap q` is the degree-one component of `q.psi`. -/
theorem degreeOneMap_spec_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    q.degreeOneMap = q.psi 1 :=
  q.degreeOneMap_spec

/-- Two triples are strictly equivalent when they have the same structure morphism and an
isomorphism of line bundles intertwining every homogeneous component of `ψ`. -/
def StrictlyEquivalent {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (q q' : DegreeOneTriple 𝒜 deg T) : Prop :=
  ∃ (h : q.morphism = q'.morphism) (β : q.lineBundle ≅ q'.lineBundle),
    ∀ n : ℕ,
      eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n)) h) ≫
          q'.psi n =
        q.psi n ≫ tensorPowerUnitMap β.hom n

/-- Strict equivalence is equality of structure morphisms together with a line-bundle
isomorphism transporting every homogeneous map. -/
theorem strictlyEquivalent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (q q' : DegreeOneTriple 𝒜 deg T) :
    StrictlyEquivalent q q' ↔
      ∃ (h : q.morphism = q'.morphism) (β : q.lineBundle ≅ q'.lineBundle),
        ∀ n : ℕ,
          eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n)) h) ≫
              q'.psi n =
            q.psi n ≫ tensorPowerUnitMap β.hom n :=
  sorry

/-- The structure morphism of the pullback of a triple along a morphism of test schemes. -/
def pullbackMorphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) : ofOver T' ⟶ X :=
  ofOverMap g ≫ q.morphism

/-- The line bundle of the pullback of a triple is the module pullback of the original
line bundle. -/
def pullbackLineBundle {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) : (ofOver T').Modules :=
  (Modules.pullback (ofOverMap g)).obj q.lineBundle

/-- Homogeneous components of the pullback of a triple. -/
def pullbackPsi {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) (n : ℕ) :
    (Modules.pullback (pullbackMorphism g q)).obj (deg.obj n) ⟶
      tensorPowerUnit (pullbackLineBundle g q) n :=
  ((AlgebraicGeometry.AlgebraicSpace.Modules.pullbackCompIso
        (ofOverMap g) q.morphism).inv.app (deg.obj n)) ≫
    (Modules.pullback (ofOverMap g)).map (q.psi n) ≫
      pullbackTensorPowerHom (ofOverMap g) q.lineBundle n

/-- The pullback-side degree-one map of a pulled-back triple. -/
def pullbackDegreeOneMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) :
    (Modules.pullback (pullbackMorphism g q)).obj (deg.obj 1) ⟶
      tensorPowerUnit (pullbackLineBundle g q) 1 :=
  pullbackPsi g q 1

/-- Pull back a degree-one triple along a morphism of test schemes. -/
def pullback {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) : DegreeOneTriple 𝒜 deg T' :=
  of (pullbackMorphism g q) (pullbackLineBundle g q) sorry (pullbackPsi g q) sorry sorry
    (pullbackDegreeOneMap g q) sorry sorry

/-- The structure morphism of `pullback g q` is `ofOverMap g ≫ q.morphism`. -/
theorem pullback_morphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) :
    (pullback g q).morphism = ofOverMap g ≫ q.morphism :=
  rfl

/-- The line bundle of `pullback g q` is the module pullback of `q.lineBundle`. -/
theorem pullback_lineBundle {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) :
    (pullback g q).lineBundle = (Modules.pullback (ofOverMap g)).obj q.lineBundle :=
  rfl

end DegreeOneTriple

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
