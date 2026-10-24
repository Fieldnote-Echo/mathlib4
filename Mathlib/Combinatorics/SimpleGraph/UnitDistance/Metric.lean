/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
module

public import Mathlib.Combinatorics.SimpleGraph.EMetricSpace
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic

/-!
# Distance bounds for unit-distance embeddings

A unit-distance embedding is 1-Lipschitz for the graph extended metric. Thus ambient distance
gives a lower bound on extended graph distance.
-/

@[expose] public section

open scoped ENNReal

namespace SimpleGraph.UnitDistEmbedding

variable {V E : Type*} {G : SimpleGraph V} [MetricSpace E] (U : G.UnitDistEmbedding E)

theorem lipschitzWith : LipschitzWith 1 (fun x : MetricVertex G => U.p x.val) := by
  apply (MetricVertex.lipschitzWith_one_iff U.p).mpr
  intro u v huv
  simp [edist_dist, U.unit_dist huv]

theorem edist_le (u v : V) :
    EDist.edist (U.p u) (U.p v) ≤ (G.edist u v : ℝ≥0∞) := by
  simpa using U.lipschitzWith ⟨u⟩ ⟨v⟩

/-- Reachability is needed because `SimpleGraph.dist` is zero between disconnected vertices. -/
theorem dist_le {u v : V} (hr : G.Reachable u v) :
    Dist.dist (U.p u) (U.p v) ≤ (G.dist u v : ℝ) := by
  apply (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp
  simpa [edist_dist, ← hr.coe_dist_eq_edist] using U.edist_le u v

end SimpleGraph.UnitDistEmbedding
