module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Rows

/-!
# Universal Properties of Milnor Rows

This leaf constructs the inverse-limit row as the kernel of the Milnor difference morphism and
the canonical first-derived-limit row as its cokernel. The universal maps are assembled
componentwise from the corresponding Milnor kernel and cokernel APIs.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe v

namespace CategoryTheory.ShortComplex.ShortExact

open SequentialInverseSystem.Milnor SequentialInverseSystem.Milnor.ProductCone

namespace LimitRow

/-- The first component of a morphism into the product row is annihilated by the corresponding
Milnor difference map. -/
theorem condition₁ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    f.τ₁ ≫ S.X₁.milnorDifferenceMap = 0 := sorry

/-- The second component of a morphism into the product row is annihilated by the corresponding
Milnor difference map. -/
theorem condition₂ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    f.τ₂ ≫ S.X₂.milnorDifferenceMap = 0 := sorry

/-- The third component of a morphism into the product row is annihilated by the corresponding
Milnor difference map. -/
theorem condition₃ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    f.τ₃ ≫ S.X₃.milnorDifferenceMap = 0 := sorry

/-- The componentwise lifts to inverse limits commute with the left map of the short complex. -/
theorem lift_comm₁₂ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    liftToLimit S.X₁ f.τ₁ (condition₁ S f h) ≫
        (S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})).f =
      W.f ≫ liftToLimit S.X₂ f.τ₂ (condition₂ S f h) := sorry

/-- The componentwise lifts to inverse limits commute with the right map of the short complex. -/
theorem lift_comm₂₃ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    liftToLimit S.X₂ f.τ₂ (condition₂ S f h) ≫
        (S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})).g =
      W.g ≫ liftToLimit S.X₃ f.τ₃ (condition₃ S f h) := sorry

/-- The explicit componentwise lift from a kernel test object to the inverse-limit row. -/
noncomputable def lift (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    W ⟶ S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}) where
  τ₁ := liftToLimit S.X₁ f.τ₁ (condition₁ S f h)
  τ₂ := liftToLimit S.X₂ f.τ₂ (condition₂ S f h)
  τ₃ := liftToLimit S.X₃ f.τ₃ (condition₃ S f h)
  comm₁₂ := lift_comm₁₂ S f h
  comm₂₃ := lift_comm₂₃ S f h

/-- `LimitRow.lift` factors the given morphism through the limit-to-product morphism. -/
theorem lift_fac (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0) :
    lift S f h ≫ limitToProductHom S = f := sorry

/-- `LimitRow.lift` is the unique factorization through the limit-to-product morphism. -/
theorem lift_uniq (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : W ⟶ productRow S)
    (h : f ≫ milnorDifferenceHom S = 0)
    (m : W ⟶ S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}))
    (hm : m ≫ limitToProductHom S = f) :
    m = lift S f h := sorry

end LimitRow

/-- The limit row is a kernel of the Milnor difference morphism between product rows. Its
universal lift is assembled componentwise from `SequentialInverseSystem.Milnor.liftToLimit`. -/
noncomputable def limitToProductHom_isLimit
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    IsLimit (KernelFork.ofι (limitToProductHom S)
      (limitToProductHom_comp_milnorDifferenceHom S)) :=
  KernelFork.IsLimit.ofι (limitToProductHom S)
    (limitToProductHom_comp_milnorDifferenceHom S)
    (fun {_} f h ↦ LimitRow.lift S f h)
    (fun {_} f h ↦ LimitRow.lift_fac S f h)
    (fun {_} f h m hm ↦ LimitRow.lift_uniq S f h m hm)

namespace R1Row

/-- The first component of a morphism out of the product row annihilates the corresponding
Milnor difference map. -/
theorem condition₁ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    S.X₁.milnorDifferenceMap ≫ f.τ₁ = 0 := sorry

/-- The second component of a morphism out of the product row annihilates the corresponding
Milnor difference map. -/
theorem condition₂ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    S.X₂.milnorDifferenceMap ≫ f.τ₂ = 0 := sorry

/-- The third component of a morphism out of the product row annihilates the corresponding
Milnor difference map. -/
theorem condition₃ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    S.X₃.milnorDifferenceMap ≫ f.τ₃ = 0 := sorry

/-- The componentwise descents from canonical Milnor cokernels commute with the left map. -/
theorem desc_comm₁₂ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    canonicalR1.desc S.X₁ f.τ₁ (condition₁ S f h) ≫ W.f =
      (r1Row S).f ≫ canonicalR1.desc S.X₂ f.τ₂ (condition₂ S f h) := sorry

/-- The componentwise descents from canonical Milnor cokernels commute with the right map. -/
theorem desc_comm₂₃ (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    canonicalR1.desc S.X₂ f.τ₂ (condition₂ S f h) ≫ W.g =
      (r1Row S).g ≫ canonicalR1.desc S.X₃ f.τ₃ (condition₃ S f h) := sorry

/-- The explicit componentwise descent from the canonical `R1` row to a cokernel test object. -/
noncomputable def desc (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    r1Row S ⟶ W where
  τ₁ := canonicalR1.desc S.X₁ f.τ₁ (condition₁ S f h)
  τ₂ := canonicalR1.desc S.X₂ f.τ₂ (condition₂ S f h)
  τ₃ := canonicalR1.desc S.X₃ f.τ₃ (condition₃ S f h)
  comm₁₂ := desc_comm₁₂ S f h
  comm₂₃ := desc_comm₂₃ S f h

/-- `R1Row.desc` factors the given morphism through the product-to-`R1` morphism. -/
theorem desc_fac (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) :
    productToR1Hom S ≫ desc S f h = f := sorry

/-- `R1Row.desc` is the unique factorization through the product-to-`R1` morphism. -/
theorem desc_uniq (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}))
    {W : ShortComplex AddCommGrpCat.{v}} (f : productRow S ⟶ W)
    (h : milnorDifferenceHom S ≫ f = 0) (m : r1Row S ⟶ W)
    (hm : productToR1Hom S ≫ m = f) :
    m = desc S f h := sorry

end R1Row

/-- The canonical `R1` row is a cokernel of the Milnor difference morphism between product
rows. Its universal descent is assembled from the canonical Milnor cokernel descents. -/
noncomputable def productToR1Hom_isColimit
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    IsColimit (CokernelCofork.ofπ (productToR1Hom S)
      (milnorDifferenceHom_comp_productToR1Hom S)) :=
  CokernelCofork.IsColimit.ofπ (productToR1Hom S)
    (milnorDifferenceHom_comp_productToR1Hom S)
    (fun {_} f h ↦ R1Row.desc S f h)
    (fun {_} f h ↦ R1Row.desc_fac S f h)
    (fun {_} f h m hm ↦ R1Row.desc_uniq S f h m hm)

end CategoryTheory.ShortComplex.ShortExact
