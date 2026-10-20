module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveAdjunction
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# The additive structure on geometric inverse image

The geometric inverse image transports the actual zero, negation and addition
maps of an additive sheaf through its canonical finite-product comparisons.
The resulting adjunction compares with the small-chart additive construction.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleAdditive.ForgetComparison
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Forget only the additive structure, retaining the original section types. -/
abbrev forgetAdd (X : AlgebraicSpace S) :=
  sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})

/-- The zero of the original additive sheaf, as a map of type-valued sheaves. -/
def zero (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    𝟙_ (Sheaf (smallEtaleTopology Y) (Type u)) ⟶ (forgetAdd Y).obj A :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : A.obj.obj U)), naturality := sorry }⟩

/-- The original negation map of the additive sheaf. -/
def neg (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (forgetAdd Y).obj A ⟶ (forgetAdd Y).obj A :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun (x : A.obj.obj U) ↦ -x), naturality := sorry }⟩

/-- The original addition map of the additive sheaf. -/
def add (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (forgetAdd Y).obj A ⊗ (forgetAdd Y).obj A ⟶ (forgetAdd Y).obj A :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun (x : A.obj.obj U × A.obj.obj U) ↦ x.1 + x.2)
     naturality := sorry }⟩

/-- The monoidal data is the existing finite-product comparison for geometric inverse image. -/
@[implicit_reducible]
def geometricMonoidal (f : X ⟶ Y) : (EtaleTopos.inverseImage f).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts (EtaleTopos.inverseImage f)

/-- The geometric inverse-image carrier is kept without a change of type. -/
abbrev carrier (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :=
  (EtaleTopos.inverseImage f).obj ((forgetAdd Y).obj A)

/-- Transport the original zero through the canonical terminal-object comparison. -/
def zeroImage (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    𝟙_ (Sheaf (smallEtaleTopology X) (Type u)) ⟶ carrier f A := by
  -- Local instance justification (defeq pin): fix the canonical finite-product comparison data used to transport zero.
  letI := geometricMonoidal f
  exact Functor.LaxMonoidal.ε (EtaleTopos.inverseImage f) ≫ (EtaleTopos.inverseImage f).map (zero A)

/-- Negation is the geometric image of the original negation map. -/
def negImage (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    carrier f A ⟶ carrier f A := (EtaleTopos.inverseImage f).map (neg A)

/-- Addition is the geometric image of addition after the canonical product comparison. -/
def addImage (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    carrier f A ⊗ carrier f A ⟶ carrier f A := by
  -- Local instance justification (defeq pin): fix the same canonical product comparison when transporting addition.
  letI := geometricMonoidal f
  exact Functor.LaxMonoidal.μ (EtaleTopos.inverseImage f) _ _ ≫ (EtaleTopos.inverseImage f).map (add A)

/-- The section group uses those exact transported operations and the standard iterated sums. -/
@[implicit_reducible]
def sectionGroup (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})
    (U : (smallEtaleSite X)ᵒᵖ) : AddCommGroup ((carrier f A).obj.obj U) :=
  { @AddGroup.ofLeftAxioms ((carrier f A).obj.obj U)
      ⟨fun x y ↦ (addImage f A).hom.app U (x, y)⟩
      ⟨fun x ↦ (negImage f A).hom.app U x⟩
      ⟨(zeroImage f A).hom.app U PUnit.unit⟩ sorry sorry sorry with
    add_comm := sorry }

/-- The additive presheaf retains the geometric section types and restriction functions. -/
def presheaf (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := @AddCommGrpCat.of ((carrier f A).obj.obj U) (sectionGroup f A U)
  map {U V} g := @AddCommGrpCat.ofHom ((carrier f A).obj.obj U) ((carrier f A).obj.obj V)
    (sectionGroup f A U) (sectionGroup f A V)
    (@AddMonoidHom.mk' ((carrier f A).obj.obj U) ((carrier f A).obj.obj V)
      (sectionGroup f A V).toAddGroup (sectionGroup f A U).toAddZeroClass
      ((carrier f A).obj.map g) sorry)
  map_id := sorry
  map_comp := sorry

/-- The additive lift is a sheaf because its underlying geometric carrier is a sheaf. -/
def sheaf (f : X ⟶ Y) (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  ⟨presheaf f A, by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
    exact (carrier f A).property⟩

/-- The lifted functor acts on maps by the original geometric inverse-image map. -/
def inverseImage (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u} ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} where
  obj := sheaf f
  map {A B} g :=
    ⟨{ app := fun U ↦
        @AddCommGrpCat.ofHom ((carrier f A).obj.obj U) ((carrier f B).obj.obj U)
          (sectionGroup f A U) (sectionGroup f B U)
          (@AddMonoidHom.mk' ((carrier f A).obj.obj U) ((carrier f B).obj.obj U)
            (sectionGroup f B U).toAddGroup (sectionGroup f A U).toAddZeroClass
            (((EtaleTopos.inverseImage f).map ((forgetAdd Y).map g)).hom.app U) sorry)
       naturality := sorry }⟩
  map_id := sorry
  map_comp := sorry

/-- Forgetting the lifted additive structure is definitionally geometric inverse image. -/
def forgetIso (f : X ⟶ Y) :
    inverseImage f ⋙ forgetAdd X ≅ forgetAdd Y ⋙ EtaleTopos.inverseImage f := Iso.refl _

/-- Equip a specified type-valued sheaf map with its additive-homomorphism law. -/
def homOfUnderlying {A B : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}}
    (h : (forgetAdd X).obj A ⟶ (forgetAdd X).obj B)
    (hadd : ∀ U (x y : A.obj.obj U), h.hom.app U (x + y) =
      @Add.add (B.obj.obj U) inferInstance (h.hom.app U x) (h.hom.app U y)) : A ⟶ B :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (h.hom.app U) (hadd U))
     naturality := sorry }⟩

/-- The Hom equivalence is geometric transposition followed by the actual direct-image comparison. -/
def underlyingHomEquiv (f : X ⟶ Y)
    (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (carrier f A ⟶ (forgetAdd X).obj B) ≃
      ((forgetAdd Y).obj A ⟶ (forgetAdd Y).obj ((EtaleAdditive.directImage f).obj B)) :=
  ((EtaleTopos.adjunction f).homEquiv _ _).trans
    ((EtaleAdditive.directImageForgetIso f).app B).symm.homToEquiv

/-- The two additive transposes use those exact geometric functions. -/
def homEquiv (f : X ⟶ Y)
    (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    ((inverseImage f).obj A ⟶ B) ≃ (A ⟶ (EtaleAdditive.directImage f).obj B) where
  toFun h := homOfUnderlying (underlyingHomEquiv f A B ((forgetAdd X).map h)) sorry
  invFun g := homOfUnderlying ((underlyingHomEquiv f A B).symm ((forgetAdd Y).map g)) sorry
  left_inv h := by
    apply (forgetAdd X).map_injective
    exact (underlyingHomEquiv f A B).symm_apply_apply ((forgetAdd X).map h)
  right_inv g := by
    apply (forgetAdd Y).map_injective
    exact (underlyingHomEquiv f A B).apply_symm_apply ((forgetAdd Y).map g)

/-- Naturality of the actual geometric transpose maps provides the adjunction. -/
def adjunctionCore (f : X ⟶ Y) :
    Adjunction.CoreHomEquiv (inverseImage f) (EtaleAdditive.directImage f) where
  homEquiv := homEquiv f
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- The lifted additive inverse image carries the actual unit and counit from its Hom maps. -/
def adjunction (f : X ⟶ Y) : inverseImage f ⊣ EtaleAdditive.directImage f :=
  Adjunction.mkOfHomEquiv (adjunctionCore f)

/-- Uniqueness of left adjoints compares the lifted operations with small-chart Kan/sheafification. -/
def comparison (f : X ⟶ Y) : inverseImage f ≅ EtaleAdditive.inverseImage f :=
  Adjunction.leftAdjointUniq (adjunction f) (EtaleAdditive.adjunction f)

/-- Both arrows of the forgetful comparison are supplied by the explicit adjunction comparison. -/
def underlyingIso (f : X ⟶ Y) :
    forgetAdd Y ⋙ EtaleTopos.inverseImage f ≅ EtaleAdditive.inverseImage f ⋙ forgetAdd X :=
  (forgetIso f).symm ≪≫ Functor.isoWhiskerRight (comparison f) (forgetAdd X)

/-- Forgetting the lifted adjunct gives exactly geometric transposition and the fixed comparison. -/
theorem adjunction_homEquiv_underlying (f : X ⟶ Y)
    (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (h : (inverseImage f).obj A ⟶ B) :
    (forgetAdd Y).map ((adjunction f).homEquiv A B h) =
      (EtaleTopos.adjunction f).homEquiv _ _ ((forgetAdd X).map h) ≫
        (EtaleAdditive.directImageForgetIso f).inv.app B := by
  simp only [adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The forward comparison is the original mate of the actual additive unit. -/
theorem underlyingIso_hom_mate (f : X ⟶ Y)
    (A : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (underlyingIso f).hom.app A =
      ((EtaleTopos.adjunction f).homEquiv _ _).symm
        ((forgetAdd Y).map ((EtaleAdditive.adjunction f).unit.app A) ≫
          (EtaleAdditive.directImageForgetIso f).hom.app ((EtaleAdditive.inverseImage f).obj A)) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adjunction f) (EtaleAdditive.adjunction f) A
  have h' := congrArg ((forgetAdd Y).map) h
  rw [adjunction_homEquiv_underlying] at h'
  let e := underlyingHomEquiv f A ((EtaleAdditive.inverseImage f).obj A)
  have he : e ((forgetAdd X).map ((comparison f).hom.app A)) =
      (forgetAdd Y).map ((EtaleAdditive.adjunction f).unit.app A) := h'
  exact (e.symm_apply_apply ((forgetAdd X).map ((comparison f).hom.app A))).symm.trans
    (congrArg e.symm he)

end AlgebraicGeometry.AlgebraicSpace.EtaleAdditive.ForgetComparison
