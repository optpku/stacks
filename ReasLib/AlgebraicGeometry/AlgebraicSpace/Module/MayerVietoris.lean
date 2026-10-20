/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LowerShriek

/-! # Mayer–Vietoris comparison maps and exactness for module sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The structure morphism `U ×_X V ⟶ X`, as `Limits.pullback.fst j f ≫ j`. -/
abbrev fiberHom {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X) :
    Limits.pullback j f ⟶ X :=
  Limits.pullback.fst j f ≫ j

/-- The two structure maps of `U ×_X V` agree as morphisms to `X`. -/
def fiberHom_eq {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X) :
    fiberHom j f = Limits.pullback.snd j f ≫ f :=
  Limits.pullback.condition

/-- Transport `j_! F|_U` along an equality of étale morphisms to `X`. -/
def lowerShriekRestrictObj_eq {W X : AlgebraicSpace S} {p q : W ⟶ X}
    [hp : Etale p] [hq : Etale q] (h : p = q) (F : X.Modules) :
    (lowerShriek p).obj (restrict F p) = (lowerShriek q).obj (restrict F q) :=
  Eq.rec (motive := fun r (_ : p = r) =>
      ∀ hr : Etale r,
        (@lowerShriek S W X p hp).obj (@restrict S W X F p hp) =
          (@lowerShriek S W X r hr).obj (@restrict S W X F r hr))
    (fun hr =>
      congrArg (fun inst : Etale p =>
          (@lowerShriek S W X p inst).obj (@restrict S W X F p inst))
        (Subsingleton.elim hp hr))
    h hq

/-- The comparison `j_{W!} F|_W ⟶ j_{U!} F|_U` of étale lower shriek along a
factorization `W ⟶ U ⟶ X`. -/
def lowerShriekRestrictHom {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    (lowerShriek (p ≫ j)).obj (restrict F (p ≫ j)) ⟶
      (lowerShriek j).obj (restrict F j) :=
  ((lowerShriekAdjunction (p ≫ j)).homEquiv (restrict F (p ≫ j))
      ((lowerShriek j).obj (restrict F j))).symm
    ((restrictFunctorComp p j).inv.app F ≫
      (restrictFunctor p).map ((lowerShriekAdjunction j).unit.app (restrict F j)) ≫
      (restrictFunctorComp p j).hom.app ((lowerShriek j).obj (restrict F j)))

/-- `lowerShriekRestrictHom` is the adjunct of the restricted unit of
`lowerShriekAdjunction j`, after identifying successive restrictions with
restriction along the composite. -/
theorem lowerShriekRestrictHom_eq {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    lowerShriekRestrictHom p j F =
      ((lowerShriekAdjunction (p ≫ j)).homEquiv (restrict F (p ≫ j))
          ((lowerShriek j).obj (restrict F j))).symm
        ((restrictFunctorComp p j).inv.app F ≫
          (restrictFunctor p).map ((lowerShriekAdjunction j).unit.app (restrict F j)) ≫
          (restrictFunctorComp p j).hom.app ((lowerShriek j).obj (restrict F j))) :=
  rfl

/-- The `U`-leg of the Mayer–Vietoris lower-shriek comparison. -/
def mayerVietorisLowerShriekιU {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) ⟶
      (lowerShriek j).obj (restrict F j) :=
  lowerShriekRestrictHom (Limits.pullback.fst j f) j F

/-- The `V`-leg of the Mayer–Vietoris lower-shriek comparison, transported along
`fiberHom_eq`. -/
def mayerVietorisLowerShriekιV {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) ⟶
      (lowerShriek f).obj (restrict F f) :=
  eqToHom (lowerShriekRestrictObj_eq (fiberHom_eq j f) F) ≫
    lowerShriekRestrictHom (Limits.pullback.snd j f) f F

/-- The first Mayer–Vietoris arrow
`j_{U×_X V!} F|_{U×_X V} ⟶ j_{U!} F|_U ⊞ j_{V!} F|_V`, with a sign on the `V`-leg. -/
def mayerVietorisLowerShriekι {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) ⟶
      biprod ((lowerShriek j).obj (restrict F j)) ((lowerShriek f).obj (restrict F f)) :=
  biprod.lift (mayerVietorisLowerShriekιU j f F) (-mayerVietorisLowerShriekιV j f F)

/-- The second Mayer–Vietoris arrow `j_{U!} F|_U ⊞ j_{V!} F|_V ⟶ F`, as the
biproduct of the two lower-shriek counits. -/
def mayerVietorisLowerShriekπ {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    biprod ((lowerShriek j).obj (restrict F j)) ((lowerShriek f).obj (restrict F f)) ⟶ F :=
  biprod.desc ((lowerShriekAdjunction j).counit.app F)
    ((lowerShriekAdjunction f).counit.app F)

/-- The three-term complex formed by the signed intersection comparison and
the sum of counits for two étale morphisms. -/
def mayerVietorisLowerShriekShortComplex {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (mayerVietorisLowerShriekι j f F) (mayerVietorisLowerShriekπ j f F) sorry

/-- The left vertex of the Mayer–Vietoris short complex is
`j_{U×_X V!} F|_{U×_X V}`. -/
theorem mayerVietorisLowerShriekShortComplex_X₁ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).X₁ =
      (lowerShriek (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  rfl

/-- The first arrow of the Mayer–Vietoris short complex is
`mayerVietorisLowerShriekι`. -/
theorem mayerVietorisLowerShriekShortComplex_f {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).f = mayerVietorisLowerShriekι j f F :=
  rfl

/-- The second arrow of the Mayer–Vietoris short complex is
`mayerVietorisLowerShriekπ`. -/
theorem mayerVietorisLowerShriekShortComplex_g {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisLowerShriekShortComplex j f F).g = mayerVietorisLowerShriekπ j f F :=
  rfl

/-- The `U`-leg comparison as a natural transformation of étale extension-by-zero
functors on `X`. -/
def mayerVietorisLowerShriekιNatTransU {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f) ⟶
      restrictFunctor j ⋙ lowerShriek j where
  app F := mayerVietorisLowerShriekιU j f F
  naturality := fun _ _ _ ↦ sorry

/-- The `V`-leg comparison as a natural transformation of étale extension-by-zero
functors on `X`. -/
def mayerVietorisLowerShriekιNatTransV {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f) ⟶
      restrictFunctor f ⋙ lowerShriek f where
  app F := mayerVietorisLowerShriekιV j f F
  naturality := fun _ _ _ ↦ sorry

/-- For an elementary distinguished square of algebraic spaces, the lower-shriek
intersection comparison and sum of counits form a short exact sequence of modules. -/
theorem mayerVietorisLowerShriek_shortExact {U V X : AlgebraicSpace S}
    (j : U ⟶ X) (f : V ⟶ X) [h : IsElementaryDistinguishedSquare j f]
    (F : X.Modules) :
    -- Local instance justification (search instability): Extract the square's open-immersion certificate because class search for IsOpenImmersion j cannot determine the opposite leg f.
    letI : IsOpenImmersion j := h.isOpenImmersion
    -- Local instance justification (search instability): Extract the square's etale certificate because class search for Etale f cannot determine the opposite leg j.
    letI : Etale f := h.isEtale
    (mayerVietorisLowerShriekShortComplex j f F).ShortExact :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
