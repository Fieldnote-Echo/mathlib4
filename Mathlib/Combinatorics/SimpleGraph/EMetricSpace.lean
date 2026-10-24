/-
Copyright (c) 2026 Nelson Spence, Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence, Snir Broshi
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The extended metric space of a graph

This file uses `SimpleGraph.MetricVertex` to connect graph distance, graph homomorphisms, and
graph balls to the extended metric space API.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace SimpleGraph

variable {V W : Type*}

/-- A copy of the vertices with the graph extended metric. This permits different graph metrics
on the same vertex type without changing an existing metric on that type. -/
@[ext]
structure MetricVertex (_G : SimpleGraph V) where
  /-- The vertex in the original graph. -/
  val : V

namespace MetricVertex

noncomputable instance (G : SimpleGraph V) : EMetricSpace (MetricVertex G) where
  edist u v := (G.edist u.val v.val : ℝ≥0∞)
  edist_self u := by simp
  edist_comm u v := by rw [SimpleGraph.edist_comm]
  edist_triangle u v w := by
    simpa using ENat.toENNReal_mono (G.edist_triangle (u := u.val) (v := v.val) (w := w.val))
  eq_of_edist_eq_zero h := by
    apply MetricVertex.ext
    exact SimpleGraph.edist_eq_zero_iff.mp (ENat.toENNReal_eq_zero.mp h)

@[simp]
theorem edist_eq (G : SimpleGraph V) (u v : MetricVertex G) :
    EDist.edist u v = (G.edist u.val v.val : ℝ≥0∞) := rfl

variable {G : SimpleGraph V}

/-- To prove a Lipschitz bound for graph distance, it suffices to check adjacent vertices.
The condition `K ≠ 0` is needed for disconnected graphs, since `0 * ∞ = 0`. -/
theorem lipschitzWith_iff_of_ne_zero {E : Type*} [PseudoEMetricSpace E]
    (f : V → E) {K : ℝ≥0} (hK : K ≠ 0) :
    LipschitzWith K (fun x : MetricVertex G => f x.val) ↔
      ∀ u v, G.Adj u v → EDist.edist (f u) (f v) ≤ K := by
  constructor
  · intro hf u v huv
    simpa [SimpleGraph.edist_eq_one_iff_adj.mpr huv] using hf ⟨u⟩ ⟨v⟩
  · intro hf ⟨u⟩ ⟨v⟩
    change EDist.edist (f u) (f v) ≤ (K : ℝ≥0∞) * (G.edist u v : ℝ≥0∞)
    by_cases hr : G.Reachable u v
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
      rw [← hp]
      simpa [mul_comm] using edist_le_range_sum_of_edist_le
        (f := fun i => f (p.getVert i)) (d := fun _ => (K : ℝ≥0∞)) p.length
        (fun hi => hf _ _ (p.adj_getVert_succ hi))
    · simp [G.edist_eq_top_of_not_reachable hr, hK]

theorem lipschitzWith_one_iff {E : Type*} [PseudoEMetricSpace E] (f : V → E) :
    LipschitzWith 1 (fun x : MetricVertex G => f x.val) ↔
      ∀ u v, G.Adj u v → EDist.edist (f u) (f v) ≤ 1 := by
  simpa using lipschitzWith_iff_of_ne_zero (G := G) f one_ne_zero

theorem mem_eball_iff (u v : V) (r : ℕ∞) :
    (⟨u⟩ : MetricVertex G) ∈ Metric.eball ⟨v⟩ (r : ℝ≥0∞) ↔ u ∈ G.ball v r := by
  simp [Metric.mem_eball, SimpleGraph.mem_ball]

end MetricVertex

theorem Hom.lipschitzWith {G : SimpleGraph V} {H : SimpleGraph W} (φ : G →g H) :
    LipschitzWith 1 (fun x : MetricVertex G => (⟨φ x.val⟩ : MetricVertex H)) := by
  intro u v
  simpa using ENat.toENNReal_mono (φ.edist_le u.val v.val)

end SimpleGraph
