module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage

/-!
# Algebraic-space covering API

Typed checks retain this import path for the shared mathematical API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (cover_presieve_mem :
  ∀ {S : Scheme.{u}} {K : Precoverage (AlgebraicSpace S)}
    {X : AlgebraicSpace S} (U : X.Cover K),
    U.presieve₀ ∈ K X)

#check (standardPrecoverage_zariski :
  ∀ (S : Scheme.{u}),
    standardPrecoverage S .zariski = zariskiPrecoverage S)

#check (standardPrecoverage_etale :
  ∀ (S : Scheme.{u}),
    standardPrecoverage S .etale = etalePrecoverage)

#check (standardPrecoverage_smooth :
  ∀ (S : Scheme.{u}),
    standardPrecoverage S .smooth = precoverage (@Smooth S))

#check (standardPrecoverage_syntomic :
  ∀ (S : Scheme.{u}),
    standardPrecoverage S .syntomic = precoverage (@Syntomic S))

#check (standardPrecoverage_fppf :
  ∀ (S : Scheme.{u}),
    standardPrecoverage S .fppf = fppfPrecoverage S)

end AlgebraicGeometry.AlgebraicSpace
