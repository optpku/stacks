module

public import stacks_project.Chap85.Definition_85_12_1_Module

/-!
# Cartesian sheaves, modules, and derived objects on C_total

A sheaf, module, or derived object on the total simplicial site is cartesian
when every simplex-operator comparison is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan

namespace Sheaf

variable {A : Type (w + 1)} [Category.{w} A]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- A sheaf on `C_total` is cartesian when `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an
isomorphism for every simplex operator `φ`. -/
class IsCartesian (F : Sheaf (topology C J) A) : Prop where
  /-- Every simplex-operator comparison `F(φ)` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (sheafTransition C J A φ F)

/-- Cartesianness of a sheaf on `C_total` is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (F : Sheaf (topology C J) A) :
    IsCartesian C J F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition C J A φ F) :=
  sorry

/-- A sheaf whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso (F : Sheaf (topology C J) A)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition C J A φ F)] :
    IsCartesian C J F where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian sheaf is an isomorphism. -/
instance instIsIso_sheafTransition (F : Sheaf (topology C J) A) [IsCartesian C J F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (sheafTransition C J A φ F) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf. -/
def transitionIso (F : Sheaf (topology C J) A) [IsCartesian C J F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((C.map φ).toFunctor.sheafPullback A (J m).toGrothendieck (J n).toGrothendieck).obj
      ((component C J A m).obj F) ≅ (component C J A n).obj F :=
  asIso (sheafTransition C J A φ F)

/-- The forward map of `transitionIso` is `sheafTransition`. -/
theorem transitionIso_hom (F : Sheaf (topology C J) A) [IsCartesian C J F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J F φ).hom = sheafTransition C J A φ F :=
  sorry

end Sheaf

/-- A sheaf of sets on `C_total` is cartesian when every `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an
isomorphism. -/
abbrev IsCartesian (F : Sheaf (topology C J) (Type w)) :=
  Sheaf.IsCartesian C J F

/-- Cartesianness of a sheaf of sets is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (F : Sheaf (topology C J) (Type w)) :
    IsCartesian C J F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (transition C J φ F) :=
  sorry

/-- A sheaf of sets whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso (F : Sheaf (topology C J) (Type w))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (transition C J φ F)] :
    IsCartesian C J F :=
  ⟨h⟩

/-- Every simplex-operator comparison of a cartesian sheaf of sets is an isomorphism. -/
instance instIsIso_transition (F : Sheaf (topology C J) (Type w)) [IsCartesian C J F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (transition C J φ F) :=
  Sheaf.IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf of sets. -/
def transitionIso (F : Sheaf (topology C J) (Type w)) [IsCartesian C J F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((C.map φ).toFunctor.sheafPullback (Type w)
      (J m).toGrothendieck (J n).toGrothendieck).obj
      ((component C J (Type w) m).obj F) ≅ (component C J (Type w) n).obj F :=
  Sheaf.transitionIso C J F φ

/-- The forward map of `transitionIso` is `transition`. -/
theorem transitionIso_hom (F : Sheaf (topology C J) (Type w)) [IsCartesian C J F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J F φ).hom = transition C J φ F :=
  sorry

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- A sheaf of abelian groups on `C_total` is cartesian when every `F(φ) : f_φ⁻¹ F_m ⟶ F_n`
is an isomorphism. -/
abbrev Abelian.IsCartesian (F : Sheaf (topology C J) AddCommGrpCat.{w}) :=
  Sheaf.IsCartesian C J F

/-- Cartesianness of a sheaf of abelian groups is equivalent to every `F(φ)` being an
isomorphism. -/
theorem abelian_isCartesian_iff (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    Abelian.IsCartesian C J F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (abelianTransition C J φ F) :=
  sorry

/-- A sheaf of abelian groups whose every simplex-operator comparison is an isomorphism
is cartesian. -/
instance instAbelianIsCartesian_of_isIso (F : Sheaf (topology C J) AddCommGrpCat.{w})
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (abelianTransition C J φ F)] :
    Abelian.IsCartesian C J F :=
  ⟨h⟩

/-- Every simplex-operator comparison of a cartesian sheaf of abelian groups is an
isomorphism. -/
instance instIsIso_abelianTransition (F : Sheaf (topology C J) AddCommGrpCat.{w})
    [Abelian.IsCartesian C J F] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (abelianTransition C J φ F) :=
  Sheaf.IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf of abelian groups. -/
def abelianTransitionIso (F : Sheaf (topology C J) AddCommGrpCat.{w})
    [Abelian.IsCartesian C J F] {m n : SimplexCategory} (φ : m ⟶ n) :
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck).obj
      ((component C J AddCommGrpCat.{w} m).obj F) ≅
    (component C J AddCommGrpCat.{w} n).obj F :=
  Sheaf.transitionIso C J F φ

/-- The forward map of `abelianTransitionIso` is `abelianTransition`. -/
theorem abelianTransitionIso_hom (F : Sheaf (topology C J) AddCommGrpCat.{w})
    [Abelian.IsCartesian C J F] {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianTransitionIso C J F φ).hom = abelianTransition C J φ F :=
  sorry

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

namespace AbelianDerived

/-- An object of `D(C_total)` is cartesian when `f_φ⁻¹ K_m ⟶ K_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) : Prop where
  /-- Every simplex-operator derived comparison is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (derivedTransition C J φ K)

/-- Cartesianness of an object of `D(C_total)` is equivalent to every simplex-operator
comparison being an isomorphism. -/
theorem isCartesian_iff
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    IsCartesian C J K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (derivedTransition C J φ K) :=
  sorry

/-- An object of `D(C_total)` whose every simplex-operator comparison is an isomorphism
is cartesian. -/
instance instIsCartesian_of_isIso
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (derivedTransition C J φ K)] :
    IsCartesian C J K where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian object of `D(C_total)` is an
isomorphism. -/
instance instIsIso_derivedTransition
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [IsCartesian C J K] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (derivedTransition C J φ K) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `f_φ⁻¹ K_m ≅ K_n` attached to a cartesian object of `D(C_total)`. -/
def transitionIso (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [IsCartesian C J K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianInverseImage C J φ).mapDerivedCategory.obj ((derivedComponent C J m).obj K) ≅
      (derivedComponent C J n).obj K :=
  asIso (derivedTransition C J φ K)

/-- The forward map of `AbelianDerived.transitionIso` is `derivedTransition`. -/
theorem transitionIso_hom
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [IsCartesian C J K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J K φ).hom = derivedTransition C J φ K :=
  sorry

end AbelianDerived

/-- An object of `D(C_total)` is cartesian when every `f_φ⁻¹ K_m ⟶ K_n` is an isomorphism. -/
abbrev Derived.IsCartesian
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :=
  AbelianDerived.IsCartesian C J K

variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

namespace Module

/-- An `O`-module on `C_total` is cartesian when `f_φ^* F_m ⟶ F_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) : Prop where
  /-- Every simplex-operator module comparison `f_φ^* F_m ⟶ F_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleTransition C J O φ F)

/-- Cartesianness of an `O`-module is equivalent to every `f_φ^* F_m ⟶ F_n` being an
isomorphism. -/
theorem isCartesian_iff
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    IsCartesian C J O F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition C J O φ F) :=
  sorry

/-- An `O`-module whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition C J O φ F)] :
    IsCartesian C J O F where
  isIso_transition := h

/-- Every simplex-operator module comparison of a cartesian `O`-module is an isomorphism. -/
instance instIsIso_moduleTransition
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [IsCartesian C J O F] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleTransition C J O φ F) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `f_φ^* F_m ≅ F_n` attached to a cartesian `O`-module. -/
def transitionIso (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [IsCartesian C J O F] {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullback.obj ((moduleComponent C J O m).obj F) ≅
      (moduleComponent C J O n).obj F :=
  asIso (moduleTransition C J O φ F)

/-- The forward map of `Module.transitionIso` is `moduleTransition`. -/
theorem transitionIso_hom
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [IsCartesian C J O F] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J O F φ).hom = moduleTransition C J O φ F :=
  sorry

end Module

namespace ModuleDerived

/-- An object of `D(O)` is cartesian when `Lf_φ^* K_m ⟶ K_n` is an isomorphism for every
simplex operator `φ`. -/
class IsCartesian
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) : Prop where
  /-- Every derived simplex-operator comparison `Lf_φ^* K_m ⟶ K_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleDerivedTransition C J O φ K)

/-- Cartesianness of an object of `D(O)` is equivalent to every `Lf_φ^* K_m ⟶ K_n` being an
isomorphism. -/
theorem isCartesian_iff (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    IsCartesian C J O K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (moduleDerivedTransition C J O φ K) :=
  sorry

/-- An object of `D(O)` whose every derived simplex-operator comparison is an isomorphism is
cartesian. -/
instance instModuleDerivedIsCartesian_of_isIso
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      IsIso (moduleDerivedTransition C J O φ K)] :
    IsCartesian C J O K where
  isIso_transition := h

/-- Every derived simplex-operator comparison of a cartesian object of `D(O)` is an
isomorphism. -/
instance instIsIso_moduleDerivedTransition
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [IsCartesian C J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleDerivedTransition C J O φ K) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `Lf_φ^* K_m ≅ K_n` attached to a cartesian object of `D(O)`. -/
def transitionIso (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [IsCartesian C J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullbackDerived.obj
        ((moduleDerivedComponent C J O m).obj K) ≅
      (moduleDerivedComponent C J O n).obj K :=
  asIso (moduleDerivedTransition C J O φ K)

/-- The forward map of `ModuleDerived.transitionIso` is `moduleDerivedTransition`. -/
theorem transitionIso_hom (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [IsCartesian C J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J O K φ).hom = moduleDerivedTransition C J O φ K :=
  sorry

end ModuleDerived

end CategoryTheory.SimplicialSites
