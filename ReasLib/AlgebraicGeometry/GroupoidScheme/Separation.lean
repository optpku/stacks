module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections

/-!
# Separation criteria for groupoid schemes

This module relates separation properties of a groupoid relation morphism to those of its
stabilizer and its identity section.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The stabilizer structure morphism is separated if and only if its identity section is a
closed immersion. -/
theorem isSeparated_stabilizerMap_iff_isClosedImmersion_one
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsSeparated G.stabilizerMap.left ↔
      IsClosedImmersion (stabilizerOneLift G).left := sorry

/-- The relation morphism is separated if and only if the stabilizer structure morphism is
separated. -/
theorem isSeparated_relationMap_iff_stabilizerMap
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsSeparated G.toPreRelation.hom.left ↔
      IsSeparated G.stabilizerMap.left := sorry

/-- The stabilizer structure morphism is quasi-separated if and only if its identity section is
quasi-compact. -/
theorem quasiSeparated_stabilizerMap_iff_quasiCompact_one
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    QuasiSeparated G.stabilizerMap.left ↔
      QuasiCompact (stabilizerOneLift G).left := sorry

/-- The relation morphism is quasi-separated if and only if the stabilizer structure morphism is
quasi-separated. -/
theorem quasiSeparated_relationMap_iff_stabilizerMap
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    QuasiSeparated G.toPreRelation.hom.left ↔
      QuasiSeparated G.stabilizerMap.left := sorry

end AlgebraicGeometry.GroupoidScheme
