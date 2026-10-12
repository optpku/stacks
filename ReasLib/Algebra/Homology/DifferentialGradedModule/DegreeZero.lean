/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Localization.Equivalence
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Modules over an Ordinary Algebra and Its Degree-Zero DGA

Complexes of ordinary right modules over `A` and differential graded modules over the
degree-zero DGA `CochainDGAlgebra.ofAlgebra R A` carry the same data.  This file gives both
concrete translations and descends them to the homotopy and derived categories.
-/

@[expose] public section

noncomputable section

universe uR uA w

open CategoryTheory ComplexShape DifferentialGradedCategory
open scoped ModuleCat.Algebra

namespace DifferentialGradedModule.DegreeZero

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [Ring A] [Algebra R A]

/-- The underlying `R`-module of one term of a complex of right `A`-modules. -/
abbrev restrictedTerm (K : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) (n : ℤ) :
    ModuleCat.{w} R :=
  (ModuleCat.restrictScalars (algebraMap R (Aᵐᵒᵖ))).obj (K.X n)

/-- The degree-zero action of `A` on a complex term, expressed through the canonical
degree-zero DGA model. -/
noncomputable def ofComplexActionZero
    (K : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) (p : ℤ) :
    restrictedTerm R A K p →ₗ[R] (CochainDGAlgebra.ofAlgebra R A).X 0 →ₗ[R]
      restrictedTerm R A K (p + 0) where
  toFun x := ModuleCat.castLinearMap (congrArg (restrictedTerm R A K) (add_zero p).symm)
    { toFun := fun a ↦ MulOpposite.op
          ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a) • x
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The homogeneous action of the degree-zero DGA on a complex of ordinary right modules. -/
noncomputable def ofComplexAction
    (K : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) (p : ℤ) : (i : ℤ) →
    restrictedTerm R A K p →ₗ[R] (CochainDGAlgebra.ofAlgebra R A).X i →ₗ[R]
      restrictedTerm R A K (p + i)
  | 0 => ofComplexActionZero R A K p
  | _ => 0

/-- A complex of ordinary right `A`-modules, regarded as a DG module over the degree-zero DGA
of `A`. -/
@[stacks 09SC "ordinary module complexes as degree-zero DG modules"]
noncomputable def ofComplex (K : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) :
    DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A) where
  X := restrictedTerm R A K
  d n := ((ModuleCat.restrictScalars (algebraMap R (Aᵐᵒᵖ))).map
    (K.d n (n + 1))).hom
  smul := ofComplexAction R A K
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- A cochain map of ordinary right modules induces a morphism of the associated degree-zero
DG modules. -/
noncomputable def ofComplexHom
    {K L : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ} (f : K ⟶ L) :
    ofComplex R A K ⟶ ofComplex R A L where
  hom n := ((ModuleCat.restrictScalars (algebraMap R (Aᵐᵒᵖ))).map (f.f n)).hom
  comm_d := sorry
  comm_smul := sorry

/-- The functor from complexes of ordinary right modules to DG modules over the degree-zero
DGA. -/
noncomputable def ofComplexFunctor :
    CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ ⥤
      DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A) where
  obj := ofComplex R A
  map := ofComplexHom R A
  map_id := sorry
  map_comp := sorry

/-- Scalar multiplication by `Aᵐᵒᵖ` recovered from the degree-zero action of a DG module. -/
@[reducible] noncomputable def toModuleSMul
    (M : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) (n : ℤ) :
    SMul (Aᵐᵒᵖ) (M.X n) where
  smul a x := cast (DifferentialGradedModule.zeroActionTarget (M := M.X) n).symm
    (M.smul n 0 x ((CochainDGAlgebra.ofAlgebraZeroIso R A).inv a.unop))

/-- The ordinary right `A`-module structure recovered on one term of a DG module over the
degree-zero DGA. -/
@[reducible] noncomputable def toModuleStructure
    (M : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) (n : ℤ) :
    Module (Aᵐᵒᵖ) (M.X n) :=
  @Module.ofMinimalAxioms (Aᵐᵒᵖ) (M.X n) inferInstance inferInstance
    (toModuleSMul R A M n) sorry sorry sorry sorry

/-- One term of a DG module over the degree-zero DGA, regarded as an ordinary right `A`-module. -/
noncomputable def toModule
    (M : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) (n : ℤ) :
    ModuleCat.{w} (Aᵐᵒᵖ) :=
  @ModuleCat.of (Aᵐᵒᵖ) inferInstance (M.X n) inferInstance (toModuleStructure R A M n)

/-- The differential of a degree-zero DG module as a morphism of ordinary right `A`-modules. -/
noncomputable def toModuleDifferential
    (M : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) (n : ℤ) :
    toModule R A M n ⟶ toModule R A M (n + 1) :=
  ModuleCat.ofHom (X := toModule R A M n) (Y := toModule R A M (n + 1))
    { toFun := M.d n
      map_add' := sorry
      map_smul' := sorry }

/-- A DG module over the degree-zero DGA, regarded as a complex of ordinary right `A`-modules. -/
@[stacks 09SC "degree-zero DG modules as ordinary module complexes"]
noncomputable def toComplex
    (M : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) :
    CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ :=
  CochainComplex.of (toModule R A M) (toModuleDifferential R A M) sorry

/-- A morphism of DG modules over the degree-zero DGA induces a cochain map of ordinary right
modules. -/
noncomputable def toComplexHom
    {M N : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)} (f : M ⟶ N) :
    toComplex R A M ⟶ toComplex R A N where
  f n := ModuleCat.ofHom (X := toModule R A M n) (Y := toModule R A N n)
    { toFun := f.hom n
      map_add' := sorry
      map_smul' := sorry }
  comm' := sorry

/-- The functor from DG modules over the degree-zero DGA to complexes of ordinary right
modules. -/
noncomputable def toComplexFunctor :
    DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A) ⥤
      CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ where
  obj := toComplex R A
  map := toComplexHom R A
  map_id := sorry
  map_comp := sorry

/-- The identity maps on the underlying terms identify conversion to a degree-zero DG module
and back with the original ordinary complex. -/
def toComplexOfComplexApp (K : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) :
    toComplex R A (ofComplex R A K) ≅ K where
  hom :=
    { f := fun n ↦ ModuleCat.ofHom
        (X := toModule R A (ofComplex R A K) n) (Y := K.X n)
        { toFun := fun x ↦ x
          map_add' := sorry
          map_smul' := sorry }
      comm' := sorry }
  inv :=
    { f := fun n ↦ ModuleCat.ofHom
        (X := K.X n) (Y := toModule R A (ofComplex R A K) n)
        { toFun := fun x ↦ x
          map_add' := sorry
          map_smul' := sorry }
      comm' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The termwise identity comparison `toComplexOfComplexApp` is natural. -/
theorem toComplexOfComplexApp_naturality
    {K L : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ} (f : K ⟶ L) :
    (ofComplexFunctor R A ⋙ toComplexFunctor R A).map f ≫
        (toComplexOfComplexApp R A L).hom =
      (toComplexOfComplexApp R A K).hom ≫ f := sorry

/-- Converting ordinary complexes to degree-zero DG modules and back is naturally isomorphic
to the identity functor. -/
def toComplexOfComplexIso :
    ofComplexFunctor R A ⋙ toComplexFunctor R A ≅
      𝟭 (CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ) :=
  NatIso.ofComponents (toComplexOfComplexApp R A)
    (fun f ↦ toComplexOfComplexApp_naturality R A f)

/-- The identity maps on the underlying graded terms identify conversion to an ordinary
complex and back with the original degree-zero DG module. -/
def ofComplexToComplexApp
    (M : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) :
    ofComplex R A (toComplex R A M) ≅ M where
  hom :=
    { hom := fun _ ↦
        { toFun := fun x ↦ x
          map_add' := sorry
          map_smul' := sorry }
      comm_d := sorry
      comm_smul := sorry }
  inv :=
    { hom := fun _ ↦
        { toFun := fun x ↦ x
          map_add' := sorry
          map_smul' := sorry }
      comm_d := sorry
      comm_smul := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The degreewise identity comparison `ofComplexToComplexApp` is natural. -/
theorem ofComplexToComplexApp_naturality
    {M N : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)} (f : M ⟶ N) :
    (toComplexFunctor R A ⋙ ofComplexFunctor R A).map f ≫
        (ofComplexToComplexApp R A N).hom =
      (ofComplexToComplexApp R A M).hom ≫ f := sorry

/-- Converting degree-zero DG modules to ordinary complexes and back is naturally isomorphic
to the identity functor. -/
def ofComplexToComplexIso :
    toComplexFunctor R A ⋙ ofComplexFunctor R A ≅
      𝟭 (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) :=
  NatIso.ofComponents (ofComplexToComplexApp R A)
    (fun f ↦ ofComplexToComplexApp_naturality R A f)

/-- The ordinary-module-to-DG-module functor identifies cochain-homotopic maps after passage to
the DG homotopy category. -/
theorem ofComplexFunctor_homotopic
    {K L : CochainComplex (ModuleCat.{w} (Aᵐᵒᵖ)) ℤ} {f g : K ⟶ L}
    (h : homotopic (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) f g) :
    (ofComplexFunctor R A ⋙
        DifferentialGradedModule.toK (CochainDGAlgebra.ofAlgebra R A)).map f =
      (ofComplexFunctor R A ⋙
        DifferentialGradedModule.toK (CochainDGAlgebra.ofAlgebra R A)).map g := sorry

/-- The homotopy functor from ordinary right-module complexes to degree-zero DG modules. -/
noncomputable abbrev toDGK :
    HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
      K R (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) :=
  CategoryTheory.Quotient.lift _
    (ofComplexFunctor R A ⋙
      DifferentialGradedModule.toK (CochainDGAlgebra.ofAlgebra R A))
    (fun _ _ _ _ h ↦ ofComplexFunctor_homotopic R A h)

/-- Forgetting a degree-zero DG-module homotopy yields an ordinary cochain homotopy. -/
theorem fromDGK_sound
    {M N : DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)}
    {f g : CompHom M N} (h : Homotopic M N f g) :
    (HomotopyCategory.quotient (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)).map
        (toComplexHom R A (DifferentialGradedModule.compHomToHom f)) =
      (HomotopyCategory.quotient (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)).map
        (toComplexHom R A (DifferentialGradedModule.compHomToHom g)) := sorry

/-- The homotopy functor from degree-zero DG modules to ordinary right-module complexes. -/
noncomputable def fromDGK :
    K R (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A)) ⥤
      HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) where
  obj M :=
    (HomotopyCategory.quotient (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)).obj
      (toComplex R A M.obj)
  map {M N} f := Quotient.lift
    (fun g : CompHom M.obj N.obj ↦
      (HomotopyCategory.quotient (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)).map
        (toComplexHom R A (DifferentialGradedModule.compHomToHom g)))
    (fun _ _ h ↦ fromDGK_sound R A h) f
  map_id := sorry
  map_comp := sorry

/-- The ordinary homotopy-category component induced by the explicit termwise identity
comparison. -/
def toFromDGKApp
    (K : HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)) :
    ((toDGK R A ⋙ fromDGK R A).obj K) ≅ K :=
  (HomotopyCategory.quotient (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)).mapIso
    (toComplexOfComplexApp R A K.as)

/-- The ordinary homotopy-category comparison `toFromDGKApp` is natural. -/
theorem toFromDGKApp_naturality
    {K L : HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)} (f : K ⟶ L) :
    (toDGK R A ⋙ fromDGK R A).map f ≫ (toFromDGKApp R A L).hom =
      (toFromDGKApp R A K).hom ≫ f := sorry

/-- The explicit ordinary-to-DG and DG-to-ordinary functors are quasi-inverse on homotopy
categories. -/
def toFromDGKIso :
    toDGK R A ⋙ fromDGK R A ≅
      𝟭 (HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)) :=
  NatIso.ofComponents (toFromDGKApp R A)
    (fun f ↦ toFromDGKApp_naturality R A f)

/-- The DG homotopy-category component induced by the explicit degreewise identity
comparison. -/
def fromToDGKApp
    (M : K R (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A))) :
    ((fromDGK R A ⋙ toDGK R A).obj M) ≅ M :=
  (DifferentialGradedModule.toK (CochainDGAlgebra.ofAlgebra R A)).mapIso
    (ofComplexToComplexApp R A M.obj)

/-- The DG homotopy-category comparison `fromToDGKApp` is natural. -/
theorem fromToDGKApp_naturality
    {M N : K R (DifferentialGradedModule.{uR, w} (CochainDGAlgebra.ofAlgebra R A))}
    (f : M ⟶ N) :
    (fromDGK R A ⋙ toDGK R A).map f ≫ (fromToDGKApp R A N).hom =
      (fromToDGKApp R A M).hom ≫ f := sorry

/-- The explicit DG-to-ordinary and ordinary-to-DG functors are quasi-inverse on homotopy
categories. -/
def fromToDGKIso :
    fromDGK R A ⋙ toDGK R A ≅
      𝟭 (K R (DifferentialGradedModule.{uR, w}
        (CochainDGAlgebra.ofAlgebra R A))) :=
  NatIso.ofComponents (fromToDGKApp R A)
    (fun f ↦ fromToDGKApp_naturality R A f)

/-- The ordinary-to-DG homotopy functor preserves quasi-isomorphisms after localization. -/
theorem toDGK_inverts_quasiIso :
    (HomotopyCategory.quasiIso (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ)).IsInvertedBy
      (toDGK R A ⋙ DifferentialGradedModule.Derived.Q
        (CochainDGAlgebra.ofAlgebra R A)) := sorry

/-- The DG-to-ordinary homotopy functor preserves quasi-isomorphisms after localization. -/
theorem fromDGK_inverts_quasiIso :
    (DifferentialGradedModule.quasiIso (CochainDGAlgebra.ofAlgebra R A)).IsInvertedBy
      (fromDGK R A ⋙
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
            DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))) := sorry

/-- The concrete comparison from the ordinary derived category of right `A`-modules to the
derived category of DG modules over the degree-zero DGA. -/
@[stacks 09SC "ordinary derived category to the degree-zero DG-derived category"]
noncomputable abbrev toDerived :
    DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)) ⥤
      DifferentialGradedModule.Derived.Category.{uR, w}
        (CochainDGAlgebra.ofAlgebra R A) :=
  Localization.lift
    (toDGK R A ⋙ DifferentialGradedModule.Derived.Q
      (CochainDGAlgebra.ofAlgebra R A))
    (toDGK_inverts_quasiIso R A)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
        DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))

/-- The concrete comparison from the degree-zero DG-derived category to the ordinary derived
category, obtained by localizing `fromDGK R A`. -/
@[stacks 09SC "degree-zero DG-derived category to the ordinary derived category"]
noncomputable abbrev fromDerived :
    DifferentialGradedModule.Derived.Category.{uR, w}
        (CochainDGAlgebra.ofAlgebra R A) ⥤
      DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)) :=
  Localization.lift
    (fromDGK R A ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ))))
    (fromDGK_inverts_quasiIso R A)
    (DifferentialGradedModule.Derived.Q (CochainDGAlgebra.ofAlgebra R A))

/-- Before localizing the ordinary homotopy category, the forward comparison followed by the
concrete inverse lift is naturally isomorphic to the ordinary localization functor. -/
noncomputable def toFromDerivedLiftIso :
    (toDGK R A ⋙ DifferentialGradedModule.Derived.Q
        (CochainDGAlgebra.ofAlgebra R A)) ⋙ fromDerived R A ≅
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ))) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toDGK R A)
      (Localization.Lifting.iso
        (DifferentialGradedModule.Derived.Q (CochainDGAlgebra.ofAlgebra R A))
          (DifferentialGradedModule.quasiIso (CochainDGAlgebra.ofAlgebra R A))
        (fromDGK R A ⋙
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
              DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))) (fromDerived R A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (toFromDGKIso R A)
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ))) ≪≫
    Functor.leftUnitor _

/-- Before localizing the DG homotopy category, the inverse comparison followed by the
concrete forward lift is naturally isomorphic to the DG localization functor. -/
noncomputable def fromToDerivedLiftIso :
    ((fromDGK R A ⋙
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
            DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))) ⋙
      toDerived R A) ≅
        DifferentialGradedModule.Derived.Q (CochainDGAlgebra.ofAlgebra R A) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fromDGK R A)
      (Localization.Lifting.iso
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
            DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))
          (HomotopyCategory.quasiIso (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ))
        (toDGK R A ⋙ DifferentialGradedModule.Derived.Q
          (CochainDGAlgebra.ofAlgebra R A)) (toDerived R A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fromToDGKIso R A)
      (DifferentialGradedModule.Derived.Q (CochainDGAlgebra.ofAlgebra R A)) ≪≫
    Functor.leftUnitor _

/-- The canonical equivalence between the ordinary derived category and the derived category
of modules over the degree-zero DGA.  Both functors and both comparison isomorphisms descend
from the explicit homotopy-category translations. -/
@[stacks 09SC "ordinary and degree-zero DG derived categories are equivalent"]
noncomputable abbrev equivalence :
    DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)) ≌
      DifferentialGradedModule.Derived.Category.{uR, w}
        (CochainDGAlgebra.ofAlgebra R A) :=
  Localization.equivalence
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
        DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))
      (HomotopyCategory.quasiIso (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ))
    (DifferentialGradedModule.Derived.Q (CochainDGAlgebra.ofAlgebra R A))
      (DifferentialGradedModule.quasiIso (CochainDGAlgebra.ofAlgebra R A))
    (toDGK R A ⋙ DifferentialGradedModule.Derived.Q
      (CochainDGAlgebra.ofAlgebra R A)) (toDerived R A)
    (fromDGK R A ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{w} (Aᵐᵒᵖ)) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{w} (Aᵐᵒᵖ)))) (fromDerived R A)
    (toFromDerivedLiftIso R A) (fromToDerivedLiftIso R A)

/-- The ordinary-to-DG degree-zero comparison is an equivalence because it is the forward
functor of `equivalence R A`. -/
instance toDerived_isEquivalence : (toDerived R A).IsEquivalence :=
  (equivalence R A).isEquivalence_functor

/-- The DG-to-ordinary degree-zero comparison is an equivalence because it is the inverse
functor of `equivalence R A`. -/
instance fromDerived_isEquivalence : (fromDerived R A).IsEquivalence :=
  (equivalence R A).isEquivalence_inverse

/-- The ordinary-to-DG degree-zero comparison is `R`-linear. -/
instance toDerived_linear : (toDerived R A).Linear R := sorry

/-- The DG-to-ordinary degree-zero comparison is `R`-linear. -/
instance fromDerived_linear : (fromDerived R A).Linear R := sorry

/-
Data audit: the `hom` and `inv` data of `toComplexOfComplexApp` and
`ofComplexToComplexApp` are termwise identity maps.  The inverse functor `fromDerived` is the
localization lift of `fromDGK`, while the unit and counit of `equivalence` are produced by
`Localization.liftNatIso` from the displayed homotopy-category comparisons.  Consequently,
the reported `sorryAx` occurs in linearity, chain-map, naturality, inverse-law, and localization
proof fields; no inverse functor is selected from `toDerived_isEquivalence`.
-/

end DifferentialGradedModule.DegreeZero
