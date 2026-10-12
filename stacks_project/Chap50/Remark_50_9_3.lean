/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernClass
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratedSubobject.AddCommGrp
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf ComplexShape Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.DeRham AlgebraicGeometry.Scheme.DeRham.LogarithmicForms

noncomputable section

universe u

/- Remark 50.9.3 (1): for `i > 0`, `Ωⁱ_[X/S,log]` is the least additive subsheaf of
`Ωⁱ_[X/S]` containing every local form `dlog(u₁) ∧ ⋯ ∧ dlog(uᵢ)`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.positive_isLeast :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (i : ℕ), 0 < i →
    IsLeast
      {G : Subobject (AlgebraicGeometry.Scheme.DeRham.additiveTerm f i) |
        CategoryTheory.Sheaf.AddCommGrpSubobject.ContainsSections G
          (fun a : Σ U : X.Opens,
            Fin i → (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U) ↦ a.1)
          (fun a ↦ AlgebraicGeometry.Scheme.DeRham.logarithmicGenerator f i a.1 a.2)}
      (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f i))

/- Remark 50.9.3 (2): `Ω⁰_[X/S,log]` is the image of the constant-integer morphism
`ℤ ⟶ 𝒶_X`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.zero_eq_image :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.Scheme.DeRham.logarithmicForms f 0 =
      imageSubobject (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.integerMap f))

/- Remark 50.9.3 (3): closedness under the differential gives the canonical morphism
`Ωⁱ_[X/S,log][-i] ⟶ Ωᵈᴿ[X/S]`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.toDeRham :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (i : ℕ),
    (HomologicalComplex.single
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (up ℕ) i).obj
        (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f i :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⟶
      AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.additiveComplex f)

/- Remark 50.9.3 (4): logarithmic forms have canonical biadditive wedge products in every
pair of degrees. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.wedge :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.WedgeMap f)

/- Remark 50.9.3 (5): after the logarithmic-subsheaf inclusion, logarithmic wedge products
agree with the ambient de Rham wedge from (50.4.0.1). -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.wedge_arrow :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)),
    (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.wedge f).map i j U x y =
      AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ambientWedgeMap f i j U x y)

/- Remark 50.9.3 (6): logarithmic wedge products are compatible with the single-degree maps
`Ωⁱ_[X/S,log][-i] ⟶ Ωᵈᴿ[X/S]`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.toDeRham_wedge :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (z : (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f (i + j) :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (hz : ((AlgebraicGeometry.Scheme.DeRham.logarithmicForms f (i + j)).arrow.hom.app (op U)).hom z =
      (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.wedge f).map i j U x y),
    ((((HomologicalComplex.singleObjXSelf (up ℕ) (i + j)
        (AlgebraicGeometry.Scheme.DeRham.logarithmicForms f (i + j) :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).inv ≫
      (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.toDeRham f (i + j)).f (i + j)).hom.app (op U)).hom
        z = AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ambientWedgeMap f i j U x y))

/- Remark 50.9.3 (7): an invertible `𝒶_X`-module has a canonical logarithmic first Chern
class in `H¹(X, Ω¹_[X/S,log])`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [Scheme.Modules.Invertible L],
    AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.H f 1 1)

/- Remark 50.9.3 (8): the comparison with truncated de Rham cohomology sends the logarithmic
first Chern class to `γ₁`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChern_toTruncated :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (C : AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernComparison f)
    (L : X.Modules) [Scheme.Modules.Invertible L],
    C.toTruncated (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass f L) =
      AlgebraicGeometry.Scheme.DeRham.gammaOne f C.chern L)

/- Remark 50.9.3 (9): the comparison with relative de Rham cohomology sends the logarithmic
first Chern class to `c₁ᵈᴿ`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChern_toDeRham :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (C : AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernComparison f)
    (L : X.Modules) [Scheme.Modules.Invertible L],
    C.toDeRhamCohomology (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass f L) =
      C.chern.deRhamFirstChern (Scheme.Modules.picardClass L))

/- Remark 50.9.3 (10): inclusion into all relative one-forms sends the logarithmic first Chern
class to `c₁ʰᵒᵈᵍᵉ`. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChern_toHodge :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (C : AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernComparison f)
    (L : X.Modules) [Scheme.Modules.Invertible L],
    C.toHodge (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass f L) =
      C.chern.hodgeFirstChern (Scheme.Modules.picardClass L))

/- Remark 50.9.3 (11): logarithmic first Chern classes are natural under pullback along a
commutative square of schemes. -/
@[stacks 0FMF] #check (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass_naturality :
  ∀ {X X' S S' : Scheme.{u}}
  {g : X' ⟶ X} {h : X ⟶ S} {h' : X' ⟶ S'} {k : S' ⟶ S}
  (sq : CommSq g h' h k)
  (P : AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernPullback sq) (L : X.Modules)
  [Scheme.Modules.Invertible L],
  P.logarithmicPullback
      (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass h L) =
    AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.firstChernClass h'
      ((Scheme.Modules.pullback g).obj L))
