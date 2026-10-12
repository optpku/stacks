/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Pairs
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.Algebra.Category.Ring.Sheaf.Kummer
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.CategoryTheory.Sites.Torsor

public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry RingedSpace
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kummer

/-- The admissible topologies are fppf, syntomic, and étale with invertible exponent. -/
@[expose]
def AdmissibleTopology (S : Scheme.{u}) (n : ℕ) (τ : StandardTopology) : Prop :=
  τ = .fppf ∨ τ = .syntomic ∨ τ = .etale ∧ IsUnit (n : Γ(S, ⊤))

/-- Pull back an equipped pair using the tensor-power and structure-module comparisons. -/
@[expose]
def Pair.pullback {S T : Scheme.{u}} {n : ℕ} (P : Pair S n) (f : T ⟶ S) : Pair T n :=
  Pair.ofData ((Modules.pullback f).obj P.lineBundle)
    (@isInvertibleObject.map S.Modules _ _ T.Modules _ _ (Modules.pullback f)
      (pullbackMonoidal f) P.lineBundle P.invertible_lineBundle)
    ((pullbackTensorPowerIso f P.lineBundle n).symm ≪≫
      (Modules.pullback f).mapIso P.trivialization ≪≫ pullbackStructureSheafIso f)

/-- Sections are universe-lifted compatible isomorphisms from the trivial pair. -/
abbrev Sections {S : Scheme.{u}} {n : ℕ} (P : Pair S n) (U : Over S) :=
  ULift.{u + 1} (PairIso (Pair.unit U.left n) (P.pullback U.hom))

/-- Restriction of a trivialization preserves the chosen tensor-power trivialization. -/
theorem sectionRes_preserves {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    {U V : Over S} (f : V ⟶ U) (x : Sections P U) :
    (pullbackStructureSheafIso f.left).symm ≪≫ (Modules.pullback f.left).mapIso x.down.hom ≪≫
      (pullbackComp f.left U.hom).app P.lineBundle ≪≫
        (pullbackCongr (Over.w f)).app P.lineBundle ∈ isomorphisms n
      (Pair.unit V.left n).trivialization (P.pullback V.hom).trivialization := sorry

/-- The restriction map on compatible local trivializations. -/
@[expose]
def sectionRes {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    {U V : Over S} (f : V ⟶ U) (x : Sections P U) : Sections P V :=
  ULift.up (PairIso.ofHom
    ((pullbackStructureSheafIso f.left).symm ≪≫ (Modules.pullback f.left).mapIso x.down.hom ≪≫
      (pullbackComp f.left U.hom).app P.lineBundle ≪≫
        (pullbackCongr (Over.w f)).app P.lineBundle)
    (sectionRes_preserves P f x))

/-- Restricting a trivialization along the identity leaves it unchanged. -/
theorem sectionRes_id {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (U : Over S) (x : Sections P U) : sectionRes P (𝟙 U) x = x := sorry

/-- Restriction of trivializations respects composition. -/
theorem sectionRes_comp {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    {U V W : Over S} (f : V ⟶ U) (g : W ⟶ V) (x : Sections P U) :
    sectionRes P (g ≫ f) x = sectionRes P g (sectionRes P f x) := sorry

/-- The presheaf of compatible local trivializations of an equipped pair. -/
@[expose]
def sectionsPresheaf {S : Scheme.{u}} {n : ℕ} (P : Pair S n) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj U := Sections P U.unop
  map f := TypeCat.ofHom (sectionRes P f.unop)
  map_id U := ConcreteCategory.hom_ext _ _ (sectionRes_id P U.unop)
  map_comp f g := ConcreteCategory.hom_ext _ _ (sectionRes_comp P f.unop g.unop)

/-- Compatible local trivializations form a sheaf on every standard big scheme site. -/
theorem sections_isSheaf {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) : Presheaf.IsSheaf (τ.overTopology S) (sectionsPresheaf P) := sorry

/-- The sheaf of compatible local trivializations of an equipped pair. -/
@[expose]
def sectionsSheaf {S : Scheme.{u}} {n : ℕ} (P : Pair S n) (τ : StandardTopology) :
    Sheaf (τ.overTopology S) (Type (u + 1)) :=
  ⟨sectionsPresheaf P, sections_isSheaf P τ⟩

/-- Read a root-of-unity sheaf section as a unit in the ordinary ring of global functions. -/
@[expose]
def rootUnit (τ : StandardTopology) (S : Scheme.{u}) (n : ℕ) (U : Over S)
    (g : (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U)) :
    Γ(U.left, ⊤)ˣ :=
  Units.map ULift.ringEquiv.toMonoidHom
    (Sheaf.unitsAddSheafUnit (AssociatedModule.bigCommStructureSheaf τ S)
      (((kernel.ι (Sheaf.unitsNsmul
      (AssociatedModule.bigCommStructureSheaf τ S) n)).hom.app (op U))
        (Sheaf.toSheafOfGroupsValue _ g)))

/-- The unit read from a root-of-unity section has nth power one. -/
theorem rootUnit_pow (τ : StandardTopology) (S : Scheme.{u}) (n : ℕ) (U : Over S)
    (g : (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U)) :
    rootUnit τ S n U g ^ n = 1 := sorry

/-- Root-of-unity scalar multiplication preserves compatible power trivializations. -/
theorem sectionAct_preserves {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S)
    (g : (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
    (x : Sections P U) :
    x.down.hom ≪≫ unitScalarIso (P.pullback U.hom).lineBundle (rootUnit τ S n U g) ∈
      isomorphisms n (Pair.unit U.left n).trivialization (P.pullback U.hom).trivialization := sorry

/-- Act on a local trivialization by a root-of-unity scalar automorphism of its target. -/
@[expose]
def sectionAct {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S)
    (g : (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
    (x : Sections P U) : Sections P U :=
  ULift.up (PairIso.ofHom
    (x.down.hom ≪≫ unitScalarIso (P.pullback U.hom).lineBundle (rootUnit τ S n U g))
    (sectionAct_preserves P τ U g x))

/-- The identity root of unity acts trivially on local trivializations. -/
theorem sectionAct_one {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S) (x : Sections P U) :
    sectionAct P τ U 1 x = x := sorry

/-- Scalar action on local trivializations respects multiplication of roots of unity. -/
theorem sectionAct_mul {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S)
    (g h : (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
    (x : Sections P U) :
    sectionAct P τ U (g * h) x = sectionAct P τ U g (sectionAct P τ U h x) := sorry

/-- The explicit roots-of-unity action on compatible local trivializations. -/
@[expose, implicit_reducible]
def sectionsMulAction {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S) :
    MulAction ((Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
      (Sections P U) where
  smul := sectionAct P τ U
  one_smul := sectionAct_one P τ U
  mul_smul := sectionAct_mul P τ U

/-- Restriction of local trivializations commutes with the roots-of-unity action. -/
theorem sectionAct_naturality {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) {U V : Over S} (f : V ⟶ U)
    (g : (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
    (x : Sections P U) :
    sectionRes P f (sectionAct P τ U g x) = sectionAct P τ V
      ((Sheaf.toSheafOfGroups
        (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.map f.op g)
      (sectionRes P f x) := sorry

/-- Roots of unity act transitively on compatible local trivializations whenever sections exist. -/
theorem sectionAct_pretransitive {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S) :
    @MulAction.IsPretransitive ((Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
      (Sections P U) (sectionsMulAction P τ U).toSMul := sorry

/-- The roots-of-unity action on compatible local trivializations is free. -/
theorem sectionAct_free {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (τ : StandardTopology) (U : Over S) :
    @IsCancelSMul ((Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)).1.obj (op U))
      (Sections P U) (sectionsMulAction P τ U).toSMul := sorry

/-- Positive-power equipped pairs have compatible local trivializations in every admissible topology. -/
theorem sections_locallyNonempty {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (h_pos : 0 < n) (τ : StandardTopology) (hτ : AdmissibleTopology S n τ) (U : Over S) :
    ∃ R : Sieve U, R ∈ τ.overTopology S U ∧
      ∀ ⦃V : Over S⦄ (f : V ⟶ U), R f → Nonempty (Sections P V) := sorry

/-- The roots-of-unity torsor of compatible local trivializations of an equipped pair. -/
@[expose]
def trivializationTorsor {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (h_pos : 0 < n) (τ : StandardTopology) (hτ : AdmissibleTopology S n τ) :
    Sheaf.Torsor (Sheaf.toSheafOfGroups
      (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)) where
  carrier := sectionsSheaf P τ
  mulAction := sectionsMulAction P τ
  act_naturality := sectionAct_naturality P τ
  isPretransitive := sectionAct_pretransitive P τ
  isCancelSMul := sectionAct_free P τ
  locallyNonempty := sections_locallyNonempty P h_pos τ hτ

/-- The trivialization torsor has compatible isomorphisms as sections and acts by scalar multiplication. -/
theorem trivializationTorsor_spec {S : Scheme.{u}} {n : ℕ} (P : Pair S n)
    (h_pos : 0 < n) (τ : StandardTopology) (hτ : AdmissibleTopology S n τ) (U : Over S) :
    (trivializationTorsor P h_pos τ hτ).Sections U = Sections P U ∧
      ∀ g x, ((trivializationTorsor P h_pos τ hτ).mulAction U).smul g x =
        sectionAct P τ U g x := sorry

end AlgebraicGeometry.Scheme.Modules.Kummer
