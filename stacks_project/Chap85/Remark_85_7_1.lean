module

public import stacks_project.Chap85.Remark_85_7_1_Fiberwise
public import stacks_project.Chap85.Remark_85_7_1_Morphism

/-!
# Remark 85.7.1

A morphism of ringed simplicial sites in Situation 85.3.3 is a pair
`(h, hSharp)` where `h` is a morphism of simplicial sites as in Remark 85.5.1
and `hSharp` is a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O`, equivalently `O' ⟶ h_total,* O`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]

namespace RingedMorphism

variable {J J' O O'}

/-- Remark 85.7.1 (1)
In Situation 85.3.3 case A, with sheaves of rings `O` on `C_total` and `O'` on
`C'_total`, a morphism of ringed simplicial sites is a pair `(h, hSharp)` where
`h` is a morphism of simplicial sites as in Remark 85.5.1 and
`hSharp : h_total⁻¹ O' ⟶ O`, equivalently `hSharp : O' ⟶ h_total,* O`, is a
homomorphism of sheaves of rings. -/
@[stacks 0DGZ]
def ofHom (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    RingedMorphism J J' O O' where
  toSimplicial := h
  structureMap := hSharp

/-- `ofHom` stores the given morphism of simplicial sites. -/
theorem ofHom_toSimplicial (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).toSimplicial = h :=
  sorry

/-- `ofHom` stores the given inverse-image homomorphism of sheaves of rings. -/
theorem ofHom_structureMap (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).structureMap = hSharp :=
  sorry

/-- Inverse-image homomorphisms `h_total⁻¹ O' ⟶ O` are equivalent to pushforward
homomorphisms `O' ⟶ h_total,* O`. -/
def structureMapEquiv (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor h).op.HasLeftKanExtension P] :
    ((total J J' h).ringInverseImage.obj O' ⟶ O) ≃
      (O' ⟶ (total J J' h).ringDirectImage.obj O) :=
  (total J J' h).ringAdjunction.homEquiv O' O

/-- Reconstructing from the adjunct pushforward map recovers `ofHom`. -/
theorem ofHom_eq_ofDirectImage (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    ofHom h hSharp = ofDirectImage (structureMapEquiv h hSharp) :=
  sorry

end RingedMorphism

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]

namespace RingedMorphism

variable {J J' O O'}

/-- Remark 85.7.1 (2)
In Situation 85.3.3 case B, with sheaves of rings `O` on `C_total` and `O'` on
`C'_total`, a morphism of ringed simplicial sites is a pair `(h, hSharp)` where
`h` is a morphism of simplicial sites as in Remark 85.5.1 and
`hSharp : h_total⁻¹ O' ⟶ O`, equivalently `hSharp : O' ⟶ h_total,* O`, is a
homomorphism of sheaves of rings. -/
@[stacks 0DGZ]
def ofHom (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor h).op.HasPointwiseRightKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    RingedMorphism J J' O O' where
  toSimplicial := h
  structureMap := hSharp

/-- `ofHom` stores the given morphism of simplicial sites. -/
theorem ofHom_toSimplicial (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor h).op.HasPointwiseRightKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).toSimplicial = h :=
  sorry

/-- `ofHom` stores the given inverse-image homomorphism of sheaves of rings. -/
theorem ofHom_structureMap (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor h).op.HasPointwiseRightKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    (ofHom h hSharp).structureMap = hSharp :=
  sorry

/-- Inverse-image homomorphisms `h_total⁻¹ O' ⟶ O` are equivalent to pushforward
homomorphisms `O' ⟶ h_total,* O`. -/
def structureMapEquiv (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor h).op.HasPointwiseRightKanExtension P] :
    ((total J J' h).ringInverseImage.obj O' ⟶ O) ≃
      (O' ⟶ (total J J' h).ringDirectImage.obj O) :=
  (total J J' h).ringAdjunction.homEquiv O' O

/-- Reconstructing from the adjunct pushforward map recovers `ofHom`. -/
theorem ofHom_eq_ofDirectImage (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (totalFunctor h).op.HasPointwiseRightKanExtension P]
    (hSharp : (total J J' h).ringInverseImage.obj O' ⟶ O) :
    ofHom h hSharp = ofDirectImage (structureMapEquiv h hSharp) :=
  sorry

end RingedMorphism

end CategoryTheory.Grothendieck
