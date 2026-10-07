module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct

/-!
# Cup products on Hodge cohomology

The wedge product on relative differential forms induces products on the bigraded Hodge
cohomology objects. The construction is available for an explicit tensor comparison model and
for the canonical model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- The relative `a`-forms, regarded as a cochain complex concentrated in degree zero. -/
noncomputable abbrev hodgeComplex (f : X ⟶ S) (a : ℕ) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj ((deRhamComplex f).X a)

/-- The derived global-sections object of the sheaf of relative `a`-forms. -/
noncomputable abbrev hodgeDerivedObject (f : X ⟶ S) (a : ℕ) :=
  (globalDerivedFunctor f).obj (hodgeComplex f a)

/-- The coefficient module `H^i(X, Ω^a_{X/S})`. -/
noncomputable abbrev hodgeCohomologyObject (f : X ⟶ S) (a : ℕ) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (coefficientModules f) i).obj
    (hodgeDerivedObject f a)

/-- The degreewise map from the tensor of two single complexes of relative forms to the
single complex on their wedge product. -/
noncomputable def hodgeWedgeComponent (f : X ⟶ S) (a b : ℕ) (n : ℤ) :
    (HomologicalComplex.tensorObj (hodgeComplex f a) (hodgeComplex f b)).X n ⟶
      (hodgeComplex f (a + b)).X n :=
  HomologicalComplex.mapBifunctorDesc fun i j h ↦
    if hi : i = 0 then
      if hj : j = 0 then
        let hn : n = 0 :=
          h.symm.trans ((congrArg₂ (· + ·) hi hj).trans (zero_add 0))
        ((HomologicalComplex.singleObjXIsoOfEq
              (up ℤ) 0 ((deRhamComplex f).X a) i hi).hom ⊗ₘ
            (HomologicalComplex.singleObjXIsoOfEq
              (up ℤ) 0 ((deRhamComplex f).X b) j hj).hom) ≫
          SheafOfModules.RingedSite.DeRham.wedgeComponent
            (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) a b ≫
          (HomologicalComplex.singleObjXIsoOfEq
            (up ℤ) 0 ((deRhamComplex f).X (a + b)) n hn).inv
      else 0
    else 0

/-- The degreewise Hodge wedge components commute with the differentials of the single
complexes. -/
theorem hodgeWedgeComponent_comm (f : X ⟶ S) (a b : ℕ) (i j : ℤ)
    (h : (up ℤ).Rel i j) :
    hodgeWedgeComponent f a b i ≫ (hodgeComplex f (a + b)).d i j =
      (HomologicalComplex.tensorObj (hodgeComplex f a) (hodgeComplex f b)).d i j ≫
        hodgeWedgeComponent f a b j := sorry

/-- The wedge product of relative forms as a morphism between degree-zero single complexes. -/
noncomputable def hodgeWedge (f : X ⟶ S) (a b : ℕ) :
    HomologicalComplex.tensorObj (hodgeComplex f a) (hodgeComplex f b) ⟶
      hodgeComplex f (a + b) :=
  HomologicalComplex.Hom.mk (hodgeWedgeComponent f a b)
    (hodgeWedgeComponent_comm f a b)

/-- The wedge-induced multiplication between the derived global-sections objects of relative
forms. -/
noncomputable def hodgeDerivedMultiplication (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(globalDerivedFunctor f).LaxMonoidal]
    (a b : ℕ) :
    hodgeDerivedObject f a ⊗ hodgeDerivedObject f b ⟶
      hodgeDerivedObject f (a + b) :=
  Functor.LaxMonoidal.μ (globalDerivedFunctor f)
      (hodgeComplex f a) (hodgeComplex f b) ≫
    (globalDerivedFunctor f).map (hodgeWedge f a b)

/-- The component cup product
`H^i(X, Ω^a_{X/S}) ⊗ H^j(X, Ω^b_{X/S}) ⟶ H^(i+j)(X, Ω^(a+b)_{X/S})`
associated to an explicit coefficient tensor model. -/
noncomputable def hodgeCupProduct (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]
    [(globalDerivedFunctor f).LaxMonoidal]
    (T : CoefficientTensorModel f) (a b : ℕ) (i j : ℤ) :
    hodgeCohomologyObject f a i ⊗ hodgeCohomologyObject f b j ⟶
      hodgeCohomologyObject f (a + b) (i + j) :=
  (i * (b : ℤ)).negOnePow •
    (CategoryTheory.derivedCohomologyProductWith
        (hD := ModuleCat.hasDerivedCategory (coefficientRing f)) T i j
        (hodgeDerivedObject f a) (hodgeDerivedObject f b) ≫
      (DerivedCategory.homologyFunctor (coefficientModules f) (i + j)).map
        ((T.tensorIsoObj (hodgeDerivedObject f a) (hodgeDerivedObject f b)).inv ≫
          hodgeDerivedMultiplication f a b))

/-- The component Hodge cup product associated to an explicit tensor model is associative. -/
theorem hodgeCupProduct_assoc (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]
    [(globalDerivedFunctor f).LaxMonoidal]
    (T : CoefficientTensorModel f)
    (a b c : ℕ) (i j k : ℤ) :
    (hodgeCupProduct f T a b i j ▷ hodgeCohomologyObject f c k) ≫
        hodgeCupProduct f T (a + b) c (i + j) k =
      (α_ (hodgeCohomologyObject f a i) (hodgeCohomologyObject f b j)
        (hodgeCohomologyObject f c k)).hom ≫
        (hodgeCohomologyObject f a i ◁ hodgeCupProduct f T b c j k) ≫
        hodgeCupProduct f T a (b + c) i (j + k) ≫
        eqToHom (congrArg₂ (hodgeCohomologyObject f)
          (Nat.add_assoc a b c).symm (add_assoc i j k).symm) := sorry

/-- The component Hodge cup product associated to an explicit tensor model is graded
commutative for total Hodge degrees. -/
theorem hodgeCupProduct_gradedComm (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)] [BraidedCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Braided]
    [(globalDerivedFunctor f).LaxBraided]
    (T : CoefficientTensorModel f)
    (a b : ℕ) (i j : ℤ) :
    hodgeCupProduct f T a b i j =
      (((a : ℤ) + i) * ((b : ℤ) + j)).negOnePow •
        ((β_ (hodgeCohomologyObject f a i)
          (hodgeCohomologyObject f b j)).hom ≫
          hodgeCupProduct f T b a j i ≫
          eqToHom (congrArg₂ (hodgeCohomologyObject f)
            (Nat.add_comm b a) (add_comm j i))) := sorry

/-- The component Hodge cup product obtained from the canonical coefficient tensor model. -/
noncomputable def canonicalHodgeCupProduct (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]
    [(globalDerivedFunctor f).LaxMonoidal]
    (a b : ℕ) (i j : ℤ) :
    hodgeCohomologyObject f a i ⊗ hodgeCohomologyObject f b j ⟶
      hodgeCohomologyObject f (a + b) (i + j) :=
  hodgeCupProduct f (coefficientTensorModel f) a b i j

/-- The canonical component Hodge cup product is associative. -/
theorem canonicalHodgeCupProduct_assoc (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Monoidal]
    [(globalDerivedFunctor f).LaxMonoidal]
    (a b c : ℕ) (i j k : ℤ) :
    (canonicalHodgeCupProduct f a b i j ▷ hodgeCohomologyObject f c k) ≫
        canonicalHodgeCupProduct f (a + b) c (i + j) k =
      (α_ (hodgeCohomologyObject f a i) (hodgeCohomologyObject f b j)
        (hodgeCohomologyObject f c k)).hom ≫
        (hodgeCohomologyObject f a i ◁ canonicalHodgeCupProduct f b c j k) ≫
        canonicalHodgeCupProduct f a (b + c) i (j + k) ≫
        eqToHom (congrArg₂ (hodgeCohomologyObject f)
          (Nat.add_assoc a b c).symm (add_assoc i j k).symm) := sorry

/-- The canonical component Hodge cup product is graded commutative for total Hodge degrees. -/
theorem canonicalHodgeCupProduct_gradedComm (f : X ⟶ S)
    [MonoidalCategory (coefficientDerived f)] [BraidedCategory (coefficientDerived f)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules f) (up ℤ) ⥤
      coefficientDerived f).Braided]
    [(globalDerivedFunctor f).LaxBraided]
    (a b : ℕ) (i j : ℤ) :
    canonicalHodgeCupProduct f a b i j =
      (((a : ℤ) + i) * ((b : ℤ) + j)).negOnePow •
        ((β_ (hodgeCohomologyObject f a i)
          (hodgeCohomologyObject f b j)).hom ≫
          canonicalHodgeCupProduct f b a j i ≫
          eqToHom (congrArg₂ (hodgeCohomologyObject f)
            (Nat.add_comm b a) (add_comm j i))) := sorry

end AlgebraicGeometry.Scheme.DeRham
