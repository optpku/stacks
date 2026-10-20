module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.MayerVietoris
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtalePullback

/-! # Mayer–Vietoris comparisons for étale module pushforward -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Transport `j_* F|_U` along an equality of étale morphisms to `X`. -/
def pushforwardRestrictObj_eq {W X : AlgebraicSpace S} {p q : W ⟶ X}
    [hp : Etale p] [hq : Etale q] (h : p = q) (F : X.Modules) :
    (pushforward p).obj (restrict F p) = (pushforward q).obj (restrict F q) :=
  Eq.rec (motive := fun r (_ : p = r) =>
      ∀ hr : Etale r,
        (@pushforward S W X p).obj (@restrict S W X F p hp) =
          (@pushforward S W X r).obj (@restrict S W X F r hr))
    (fun hr =>
      congrArg (fun inst : Etale p =>
          (@pushforward S W X p).obj (@restrict S W X F p inst))
        (Subsingleton.elim hp hr))
    h hq

/-- The comparison `j_* F|_U ⟶ j_{W*} F|_W` of étale pushforward along a factorization
`W ⟶ U ⟶ X`. -/
def pushforwardRestrictHom {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    (pushforward j).obj (restrict F j) ⟶
      (pushforward (p ≫ j)).obj (restrict F (p ≫ j)) :=
  ((restrictAdjunction (p ≫ j)).homEquiv
      ((pushforward j).obj (restrict F j)) (restrict F (p ≫ j)))
    ((restrictFunctorComp p j).inv.app ((pushforward j).obj (restrict F j)) ≫
      (restrictFunctor p).map ((restrictAdjunction j).counit.app (restrict F j)) ≫
      (restrictFunctorComp p j).hom.app F)

/-- `pushforwardRestrictHom` is the adjunct of the restricted counit of
`restrictAdjunction j`, after identifying successive restrictions with restriction
along the composite. -/
theorem pushforwardRestrictHom_eq {W U X : AlgebraicSpace S} (p : W ⟶ U) [Etale p]
    (j : U ⟶ X) [Etale j] (F : X.Modules) :
    pushforwardRestrictHom p j F =
      ((restrictAdjunction (p ≫ j)).homEquiv
          ((pushforward j).obj (restrict F j)) (restrict F (p ≫ j)))
        ((restrictFunctorComp p j).inv.app ((pushforward j).obj (restrict F j)) ≫
          (restrictFunctor p).map ((restrictAdjunction j).counit.app (restrict F j)) ≫
          (restrictFunctorComp p j).hom.app F) :=
  rfl

/-- The `U`-leg unit of the Mayer–Vietoris pushforward comparison. -/
def mayerVietorisPushforwardιU {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    F ⟶ (pushforward j).obj (restrict F j) :=
  (restrictAdjunction j).unit.app F

/-- The `V`-leg unit of the Mayer–Vietoris pushforward comparison. -/
def mayerVietorisPushforwardιV {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    F ⟶ (pushforward f).obj (restrict F f) :=
  (restrictAdjunction f).unit.app F

/-- The first Mayer–Vietoris arrow
`F ⟶ j_{U,*} F|_U ⊞ j_{V,*} F|_V`. -/
def mayerVietorisPushforwardι {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    F ⟶ biprod ((pushforward j).obj (restrict F j)) ((pushforward f).obj (restrict F f)) :=
  biprod.lift (mayerVietorisPushforwardιU j f F) (mayerVietorisPushforwardιV j f F)

/-- The `U`-leg overlap restriction of the Mayer–Vietoris pushforward comparison. -/
def mayerVietorisPushforwardπU {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (pushforward j).obj (restrict F j) ⟶
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  pushforwardRestrictHom (Limits.pullback.fst j f) j F

/-- The `V`-leg overlap restriction of the Mayer–Vietoris pushforward comparison,
transported along `fiberHom_eq`. -/
def mayerVietorisPushforwardπV {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (pushforward f).obj (restrict F f) ⟶
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  pushforwardRestrictHom (Limits.pullback.snd j f) f F ≫
    eqToHom (pushforwardRestrictObj_eq (fiberHom_eq j f).symm F)

/-- The second Mayer–Vietoris arrow
`j_{U,*} F|_U ⊞ j_{V,*} F|_V ⟶ j_{U×_X V,*} F|_{U×_X V}`, with a sign on the `V`-leg. -/
def mayerVietorisPushforwardπ {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] (F : X.Modules) :
    biprod ((pushforward j).obj (restrict F j)) ((pushforward f).obj (restrict F f)) ⟶
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  biprod.desc (mayerVietorisPushforwardπU j f F) (-mayerVietorisPushforwardπV j f F)

/-- The diagonal adjunction unit followed by the difference of overlap restrictions is zero. -/
theorem mayerVietorisPushforward_ι_comp_π {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    mayerVietorisPushforwardι j f F ≫ mayerVietorisPushforwardπ j f F = 0 :=
  sorry

/-- The three-term complex of module pushforwards for a pair of étale morphisms. -/
def mayerVietorisPushforwardShortComplex {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (mayerVietorisPushforwardι j f F) (mayerVietorisPushforwardπ j f F)
    (mayerVietorisPushforward_ι_comp_π j f F)

/-- The left vertex of the Mayer–Vietoris short complex is `F`. -/
theorem mayerVietorisPushforwardShortComplex_X₁ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).X₁ = F :=
  rfl

/-- The middle vertex of the Mayer–Vietoris short complex is
`j_{U,*} F|_U ⊞ j_{V,*} F|_V`. -/
theorem mayerVietorisPushforwardShortComplex_X₂ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).X₂ =
      biprod ((pushforward j).obj (restrict F j)) ((pushforward f).obj (restrict F f)) :=
  rfl

/-- The right vertex of the Mayer–Vietoris short complex is
`j_{U×_X V,*} F|_{U×_X V}`. -/
theorem mayerVietorisPushforwardShortComplex_X₃ {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).X₃ =
      (pushforward (fiberHom j f)).obj (restrict F (fiberHom j f)) :=
  rfl

/-- The first arrow of the Mayer–Vietoris short complex is `mayerVietorisPushforwardι`. -/
theorem mayerVietorisPushforwardShortComplex_f {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).f = mayerVietorisPushforwardι j f F :=
  rfl

/-- The second arrow of the Mayer–Vietoris short complex is `mayerVietorisPushforwardπ`. -/
theorem mayerVietorisPushforwardShortComplex_g {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).g = mayerVietorisPushforwardπ j f F :=
  rfl

/-- The `U`-leg unit as a natural transformation `𝟭 ⟶ j_* j^*`. -/
def mayerVietorisPushforwardιNatTransU {U X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] :
    𝟭 X.Modules ⟶ restrictFunctor j ⋙ pushforward j :=
  (restrictAdjunction j).unit

/-- The `V`-leg unit as a natural transformation `𝟭 ⟶ f_* f^*`. -/
def mayerVietorisPushforwardιNatTransV {V X : AlgebraicSpace S} (f : V ⟶ X)
    [Etale f] :
    𝟭 X.Modules ⟶ restrictFunctor f ⋙ pushforward f :=
  (restrictAdjunction f).unit

/-- Overlap restriction from the `U`-leg commutes with morphisms of module sheaves. -/
theorem mayerVietorisPushforwardπNatTransU_naturality {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    {F G : X.Modules} (φ : F ⟶ G) :
    (restrictFunctor j ⋙ pushforward j).map φ ≫ mayerVietorisPushforwardπU j f G =
      mayerVietorisPushforwardπU j f F ≫
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).map φ :=
  sorry

/-- The `U`-leg overlap restriction as a natural transformation of étale pushforwards
on `X`. -/
def mayerVietorisPushforwardπNatTransU {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor j ⋙ pushforward j ⟶
      restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f) where
  app F := mayerVietorisPushforwardπU j f F
  naturality := fun _ _ φ ↦ mayerVietorisPushforwardπNatTransU_naturality j f φ

/-- Overlap restriction from the `V`-leg commutes with morphisms of module sheaves. -/
theorem mayerVietorisPushforwardπNatTransV_naturality {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    {F G : X.Modules} (φ : F ⟶ G) :
    (restrictFunctor f ⋙ pushforward f).map φ ≫ mayerVietorisPushforwardπV j f G =
      mayerVietorisPushforwardπV j f F ≫
        (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).map φ :=
  sorry

/-- The `V`-leg overlap restriction as a natural transformation of étale pushforwards
on `X`. -/
def mayerVietorisPushforwardπNatTransV {U V X : AlgebraicSpace S} (j : U ⟶ X)
    [Etale j] (f : V ⟶ X) [Etale f] :
    restrictFunctor f ⋙ pushforward f ⟶
      restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f) where
  app F := mayerVietorisPushforwardπV j f F
  naturality := fun _ _ φ ↦ mayerVietorisPushforwardπNatTransV_naturality j f φ

/-- For an elementary distinguished square, the canonical module pushforward
Mayer–Vietoris sequence is short exact. -/
theorem mayerVietorisPushforward_shortExact {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : X.Modules) :
    (mayerVietorisPushforwardShortComplex j f F).ShortExact :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
