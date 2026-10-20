/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.OffDiagonal

/-! # Exterior powers and off-diagonal sign-semi-invariant sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The `i`-th projection of an off-diagonal slice morphism `V ⟶ W ⊂ U^{×_X n}` as a
slice morphism `V ⟶ U` over `X`. -/
noncomputable def offDiagonalSliceπ {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] {n : ℕ} {V : smallEtaleSite X}
    (φ : SliceHom (offDiagonalToBase f n) V) (i : Fin n) : SliceHom f V where
  hom := φ.hom ≫ offDiagonalι f n ≫ selfFibrePowerπ f n i
  w := sorry

/-- `offDiagonalSliceπ` is postcomposition with the off-diagonal inclusion and the
`i`-th fibre-power projection. -/
theorem offDiagonalSliceπ_hom {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f]
    {n : ℕ} {V : smallEtaleSite X}
    (φ : SliceHom (offDiagonalToBase f n) V) (i : Fin n) :
    (offDiagonalSliceπ f φ i).hom =
      φ.hom ≫ offDiagonalι f n ≫ selfFibrePowerπ f n i :=
  rfl

/-- Presheaf-level alternating comparison sending a map into `W` to the wedge of its
`n` projections into `U`, via `ModuleCat.exteriorPower.mk`. -/
noncomputable def offDiagonalExteriorPresheaf {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) :
    integerExtensionPresheaf (offDiagonalToBase f n) ⟶
      integerExtensionPresheaf f ⋙ ModuleCat.exteriorPower.functor integerModule n where
  app V :=
    ModuleCat.freeDesc
      (↾fun φ : SliceHom (offDiagonalToBase f n) (unop V) ↦
        ModuleCat.exteriorPower.mk fun i ↦ ModuleCat.freeMk (offDiagonalSliceπ f φ i))
  naturality := sorry

/-- The component of `offDiagonalExteriorPresheaf` is `freeDesc` of the wedge of
projected slice morphisms. -/
theorem offDiagonalExteriorPresheaf_app {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) (V : (smallEtaleSite X)ᵒᵖ) :
    (offDiagonalExteriorPresheaf f n).app V =
      ModuleCat.freeDesc
        (↾fun φ : SliceHom (offDiagonalToBase f n) (unop V) ↦
          ModuleCat.exteriorPower.mk fun i ↦ ModuleCat.freeMk (offDiagonalSliceπ f φ i)) :=
  rfl

/-- Sheafification of the alternating comparison on free integer extension-by-zero. -/
noncomputable def offDiagonalExteriorSheaf {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) :
    freeExtensionByZeroInteger (offDiagonalToBase f n) ⟶
      (presheafToSheaf (smallEtaleTopology X) IntegerModuleCat).obj
        (integerExtensionPresheaf f ⋙ ModuleCat.exteriorPower.functor integerModule n) :=
  (presheafToSheaf (smallEtaleTopology X) IntegerModuleCat).map
    (offDiagonalExteriorPresheaf f n)

/-- `offDiagonalExteriorSheaf` is sheafification of `offDiagonalExteriorPresheaf`. -/
theorem offDiagonalExteriorSheaf_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Separated f] (n : ℕ) :
    offDiagonalExteriorSheaf f n =
      (presheafToSheaf (smallEtaleTopology X) IntegerModuleCat).map
        (offDiagonalExteriorPresheaf f n) :=
  rfl

/-- The underlying `integerModule`-module of a section of `extensionByZeroInteger f`. -/
noncomputable def extensionByZeroIntegerSectionModule {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (V : (smallEtaleSite X)ᵒᵖ) : IntegerModuleCat :=
  @ModuleCat.of integerModule inferInstance
    (((SheafOfModules.toSheaf (constantIntegerRingSheaf X).ringSheafOfComm).obj
        (extensionByZeroInteger f)).obj.obj V)
    inferInstance
    (instModuleULiftIntOfAddCommGrpCat
      (((SheafOfModules.toSheaf (constantIntegerRingSheaf X).ringSheafOfComm).obj
          (extensionByZeroInteger f)).obj.obj V))

/-- `extensionByZeroIntegerSectionModule` is `ModuleCat.of` the underlying abelian
section of `extensionByZeroInteger f`. -/
theorem extensionByZeroIntegerSectionModule_eq {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (V : (smallEtaleSite X)ᵒᵖ) :
    extensionByZeroIntegerSectionModule f V =
      @ModuleCat.of integerModule inferInstance
        (((SheafOfModules.toSheaf (constantIntegerRingSheaf X).ringSheafOfComm).obj
            (extensionByZeroInteger f)).obj.obj V)
        inferInstance
        (instModuleULiftIntOfAddCommGrpCat
          (((SheafOfModules.toSheaf (constantIntegerRingSheaf X).ringSheafOfComm).obj
              (extensionByZeroInteger f)).obj.obj V)) :=
  rfl

/-- The integer-module identification of a section of `moduleExtensionByZeroInteger f`
with a section of `extensionByZeroInteger f`. -/
noncomputable def moduleExtensionToIntegerRestrict {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (V : (smallEtaleSite X)ᵒᵖ) :
    (moduleExtensionByZeroInteger f).obj.obj V ⟶
      extensionByZeroIntegerSectionModule f V :=
  ModuleCat.ofHom
    { toFun := fun m ↦
        ConcreteCategory.hom ((extensionByZeroInteger_toSheafIso f).inv.hom.app V)
          (ConcreteCategory.hom
            ((moduleExtensionByZeroInteger_toAbelian f).hom.hom.app V) m)
      map_add' := sorry
      map_smul' := sorry }

/-- `moduleExtensionToIntegerRestrict` evaluates as the pointwise adjunct of the
integer-module forgetful identification of `f_! ℤ̲`. -/
theorem moduleExtensionToIntegerRestrict_apply {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (V : (smallEtaleSite X)ᵒᵖ)
    (m : (moduleExtensionByZeroInteger f).obj.obj V) :
    moduleExtensionToIntegerRestrict f V m =
      ConcreteCategory.hom ((extensionByZeroInteger_toSheafIso f).inv.hom.app V)
        (ConcreteCategory.hom
          ((moduleExtensionByZeroInteger_toAbelian f).hom.hom.app V) m) :=
  rfl

/-- Ring homomorphism `integerModule ⟶ 𝒪(V)` from the sheafification unit of the
constant integer ring sheaf. -/
noncomputable def integerModuleToConstRing (X : AlgebraicSpace S)
    (V : (smallEtaleSite X)ᵒᵖ) :
    integerModule →+* (constantIntegerRingSheaf X).obj.obj V :=
  (((sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}).unit.app
        ((Functor.const ((smallEtaleSite X)ᵒᵖ)).obj
          (CommRingCat.of (ULift.{u + 1} ℤ)))).app V).hom

/-- `integerModuleToConstRing` is the section of the constant-ring sheafification unit. -/
theorem integerModuleToConstRing_eq (X : AlgebraicSpace S)
    (V : (smallEtaleSite X)ᵒᵖ) :
    integerModuleToConstRing X V =
      (((sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}).unit.app
            ((Functor.const ((smallEtaleSite X)ᵒᵖ)).obj
              (CommRingCat.of (ULift.{u + 1} ℤ)))).app V).hom :=
  rfl

/-- A section of `extensionByZeroInteger f`, as an `integerModule`-module, maps to the
restriction of scalars of the commutative section module. -/
noncomputable def sectionModuleToRinged {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (V : (smallEtaleSite X)ᵒᵖ) :
    extensionByZeroIntegerSectionModule f V ⟶
      (ModuleCat.restrictScalars (integerModuleToConstRing X V)).obj
        ((extensionByZeroInteger f).val.obj V) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ x
      map_add' := sorry
      map_smul' := sorry }

/-- `sectionModuleToRinged` is the pointwise identity on underlying additive sections. -/
theorem sectionModuleToRinged_apply {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (V : (smallEtaleSite X)ᵒᵖ)
    (x : extensionByZeroIntegerSectionModule f V) :
    sectionModuleToRinged f V x = x :=
  sorry

/-- Underlying additive comparison from the integer-module exterior power of a
section of `extensionByZeroInteger f` to a section of `K^p`. -/
noncomputable def sectionExteriorToKoszul {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] (p : ℕ) (V : (smallEtaleSite X)ᵒᵖ) :
    (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).obj
        ((ModuleCat.exteriorPower.functor integerModule (p + 1)).obj
          (extensionByZeroIntegerSectionModule f V)) ⟶
      ((sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((koszulComplex f).X p)).obj V :=
  (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).map
      (ModuleCat.exteriorPower.mapRestrictScalars (integerModuleToConstRing X V)
        (sectionModuleToRinged f V) (p + 1)) ≫
    (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).map
      ((ModuleCat.restrictScalars (integerModuleToConstRing X V)).map
        ((moduleSheafificationUnitToVal.{u + 1, u, u + 1, u + 1}
            (constantIntegerRingSheaf X)
            (ExteriorPower.presheaf (constantIntegerRingSheaf X)
              (extensionByZeroInteger f) (p + 1))).app V))

/-- Sectionwise exterior powers of the free integer model of `f_! ℤ̲` map to the
underlying additive presheaf of `K^p`. -/
noncomputable def freeExteriorToKoszulPresheaf {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] (p : ℕ) :
    integerExtensionPresheaf f ⋙
        ModuleCat.exteriorPower.functor integerModule (p + 1) ⋙
        forget₂ IntegerModuleCat AddCommGrpCat.{u + 1} ⟶
      (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        ((koszulComplex f).X p) where
  app V :=
    (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).map
        (ModuleCat.exteriorPower.map
          (((sheafificationAdjunction (smallEtaleTopology X) IntegerModuleCat).unit.app
                (integerExtensionPresheaf f) ≫
              (sheafToPresheaf (smallEtaleTopology X) IntegerModuleCat).map
                (ExtensionByZeroInteger.freeIso f).hom).app V) (p + 1)) ≫
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).map
        (ModuleCat.exteriorPower.map (moduleExtensionToIntegerRestrict f V) (p + 1)) ≫
      sectionExteriorToKoszul f p V
  naturality := sorry

/-- `freeExteriorToKoszulPresheaf` is exterior power of the free-to-canonical
comparison of `f_! ℤ̲`, followed by the additive identification into `K^p`. -/
theorem freeExteriorToKoszulPresheaf_app {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] (p : ℕ) (V : (smallEtaleSite X)ᵒᵖ) :
    (freeExteriorToKoszulPresheaf f p).app V =
      (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).map
          (ModuleCat.exteriorPower.map
            (((sheafificationAdjunction (smallEtaleTopology X) IntegerModuleCat).unit.app
                  (integerExtensionPresheaf f) ≫
                (sheafToPresheaf (smallEtaleTopology X) IntegerModuleCat).map
                  (ExtensionByZeroInteger.freeIso f).hom).app V) (p + 1)) ≫
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1}).map
          (ModuleCat.exteriorPower.map (moduleExtensionToIntegerRestrict f V)
            (p + 1)) ≫
        sectionExteriorToKoszul f p V :=
  rfl

/-- The maximal `S_{p+1}`-anti-invariant quotient
`(W_p → X)_! ℤ̲ ⟶ ∧^{p+1}(f_! ℤ̲)`, as the free alternating comparison of
off-diagonal slices, transported along `freeIso` and `toAbelian` into the
underlying abelian sheaf of `ExteriorPower.sheaf` of `extensionByZeroInteger f`,
i.e. into `(koszulComplex f).X p`. -/
noncomputable def offDiagonalToKoszul {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ) :
    (abelianExtensionByZero (offDiagonalToBase f (p + 1))).obj
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f (p + 1)))) ⟶
      (koszulComplex f).X p :=
  (moduleExtensionByZeroInteger_toAbelian (offDiagonalToBase f (p + 1))).inv ≫
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).map
      (ExtensionByZeroInteger.freeIso (offDiagonalToBase f (p + 1))).inv ≫
    (sheafCompose (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).map
      (offDiagonalExteriorSheaf f (p + 1)) ≫
    (sheafComposeNatIso (smallEtaleTopology X)
        (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})
        (sheafificationAdjunction (smallEtaleTopology X) IntegerModuleCat)
        (sheafificationAdjunction (smallEtaleTopology X)
          AddCommGrpCat.{u + 1})).inv.app
      (integerExtensionPresheaf f ⋙
        ModuleCat.exteriorPower.functor integerModule (p + 1)) ≫
    (presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
      (freeExteriorToKoszulPresheaf f p) ≫
    (sheafificationAdjunction (smallEtaleTopology X)
        AddCommGrpCat.{u + 1}).counit.app ((koszulComplex f).X p)

/-- `offDiagonalToKoszul` is the free alternating comparison of off-diagonal slices,
transported along `freeIso`, `toAbelian`, and the sheafification identification
of `ExteriorPower.sheaf` into `K^p = (koszulComplex f).X p`. -/
theorem offDiagonalToKoszul_eq {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] [Separated f] (p : ℕ) :
    offDiagonalToKoszul f p =
      (moduleExtensionByZeroInteger_toAbelian (offDiagonalToBase f (p + 1))).inv ≫
        (sheafCompose (smallEtaleTopology X)
            (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).map
          (ExtensionByZeroInteger.freeIso (offDiagonalToBase f (p + 1))).inv ≫
        (sheafCompose (smallEtaleTopology X)
            (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})).map
          (offDiagonalExteriorSheaf f (p + 1)) ≫
        (sheafComposeNatIso (smallEtaleTopology X)
            (forget₂ IntegerModuleCat AddCommGrpCat.{u + 1})
            (sheafificationAdjunction (smallEtaleTopology X) IntegerModuleCat)
            (sheafificationAdjunction (smallEtaleTopology X)
              AddCommGrpCat.{u + 1})).inv.app
          (integerExtensionPresheaf f ⋙
            ModuleCat.exteriorPower.functor integerModule (p + 1)) ≫
        (presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
          (freeExteriorToKoszulPresheaf f p) ≫
        (sheafificationAdjunction (smallEtaleTopology X)
            AddCommGrpCat.{u + 1}).counit.app ((koszulComplex f).X p) :=
  rfl

/-- The off-diagonal comparison `(W → X)_! ℤ̲ ⟶ K^p` is an epimorphism. -/
instance instEpi_offDiagonalToKoszul {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] [Separated f] (p : ℕ) : Epi (offDiagonalToKoszul f p) :=
  sorry

/-- Adjunction identification of `Hom((W → X)_! ℤ̲, F)` with `F(W)`. -/
noncomputable def offDiagonalGlobalSectionsIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (preadditiveYoneda.obj F).obj
        (op ((abelianExtensionByZero (offDiagonalToBase f n)).obj
          (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n))))) ≅
      (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) where
  hom :=
    AddCommGrpCat.ofHom
      { toFun :=
          (abelianExtensionByZero_adjunction (offDiagonalToBase f n)).homEquiv
            (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n))) F
        map_zero' := sorry
        map_add' := sorry }
  inv :=
    AddCommGrpCat.ofHom
      { toFun :=
          ((abelianExtensionByZero_adjunction (offDiagonalToBase f n)).homEquiv
            (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n))) F).symm
        map_zero' := sorry
        map_add' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The adjunction comparison evaluates as the extension-by-zero adjunction equivalence. -/
theorem offDiagonalGlobalSectionsIso_hom_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (φ : (abelianExtensionByZero (offDiagonalToBase f n)).obj
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1}
        (smallEtaleTopology (offDiagonal f n))) ⟶ F) :
    (offDiagonalGlobalSectionsIso f n F).hom φ =
      (abelianExtensionByZero_adjunction (offDiagonalToBase f n)).homEquiv
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1}
          (smallEtaleTopology (offDiagonal f n))) F φ :=
  rfl

/-- The comparison `Hom(K^p, F)` to sign-semi-invariant off-diagonal sections given by precomposition
with `offDiagonalToKoszul` and the extension-by-zero adjunction. -/
noncomputable def homKoszul_antiInvariantsHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] [Separated f] (p : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (preadditiveYoneda.obj F).obj (op ((koszulComplex f).X p)) ⟶
      IntegerCharacter.invariants (offDiagonalSectionsAction f (p + 1) F) (IntegerCharacter.permutationSign (p + 1)) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦
        ⟨(offDiagonalGlobalSectionsIso f (p + 1) F).hom
          ((preadditiveYoneda.obj F).map (offDiagonalToKoszul f p).op φ), sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The inverse comparison, descending an anti-invariant section along the epimorphism
`offDiagonalToKoszul`. -/
noncomputable def homKoszul_antiInvariantsInv {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] [Separated f] (p : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IntegerCharacter.invariants (offDiagonalSectionsAction f (p + 1) F) (IntegerCharacter.permutationSign (p + 1)) ⟶
      (preadditiveYoneda.obj F).obj (op ((koszulComplex f).X p)) :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦
        CategoryTheory.Abelian.epiDesc (offDiagonalToKoszul f p)
          ((offDiagonalGlobalSectionsIso f (p + 1) F).inv
            (IntegerCharacter.inclusion (offDiagonalSectionsAction f (p + 1) F)
              (IntegerCharacter.permutationSign (p + 1)) a))
          sorry
      map_zero' := sorry
      map_add' := sorry }

/-- For a surjective étale separated morphism, Hom from the exterior power of
extension by zero is the group of sign-semi-invariant off-diagonal sections. -/
noncomputable def homKoszul_antiInvariants {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (preadditiveYoneda.obj F).obj (op ((koszulComplex f).X p)) ≅
      IntegerCharacter.invariants (offDiagonalSectionsAction f (p + 1) F) (IntegerCharacter.permutationSign (p + 1)) where
  hom := homKoszul_antiInvariantsHom f p F
  inv := homKoszul_antiInvariantsInv f p F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `homKoszul_antiInvariants` is `homKoszul_antiInvariantsHom`. -/
theorem homKoszul_antiInvariants_hom {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (homKoszul_antiInvariants f p F).hom = homKoszul_antiInvariantsHom f p F :=
  rfl

/-- Functoriality of the Hom identification in the abelian sheaf `F`. -/
theorem homKoszul_antiInvariants_natural {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (preadditiveYoneda.map φ).app (op ((koszulComplex f).X p)) ≫
        (homKoszul_antiInvariants f p G).hom =
      (homKoszul_antiInvariants f p F).hom ≫ offDiagonalAntiInvariantsMap f (p + 1) φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
