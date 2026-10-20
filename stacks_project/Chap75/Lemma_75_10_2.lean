module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.MayerVietoris.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Pushforward

/-! # Mayer–Vietoris sequence for étale pushforward -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Pretriangulated

universe u

/- Lemma 75.10.2 (1). For an elementary distinguished square of algebraic spaces,
every sheaf of structure modules has the canonical short exact sequence
0 → F → j_{U,*} F|_U ⊞ j_{V,*} F|_V → j_{U×_X V,*} F|_{U×_X V} → 0. -/
@[stacks 08GW] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforward_shortExact :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
      (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
      [IsElementaryDistinguishedSquare j f] (F : X.Modules),
      (mayerVietorisPushforwardShortComplex j f F).ShortExact)

/- Lemma 75.10.2 (2). For every object E of the unbounded derived module category,
the canonical triangle E → Rj_{U,*} E|_U ⊞ Rj_{V,*} E|_V →
Rj_{U×_X V,*} E|_{U×_X V} → E[1] is distinguished. -/
@[stacks 08GW] #check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforward_mem_distTriang :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X),
    mayerVietorisPushforwardTriangle j f E ∈ distTriang (ModuleDerived X))
