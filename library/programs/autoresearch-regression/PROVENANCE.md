# Regression consumer provenance

Application search and fitting policy derives from the public-source quadratic
consumer at SIGIL commit 976fd697ae2251207fc8e2a4479b45f9954638bf. Its directories
and package revisions remain unchanged. This separate consumer changes the
objective, data/task identities, per-workload step bound and reporting only;
the reusable providers retain their exact versions and hashes.

The fixed observations are synthetic, authored for this example. They contain
no private research data. PyTorch CPU float64 independently computes regression
gradients from individual observations; native SIGIL uses the existing bounded
reverse-mode library and full-batch gradient sufficient statistics. No Q16
trajectory equivalence, tensor-engine equivalence or training improvement is
claimed. Source remains MIT OR Apache-2.0.
