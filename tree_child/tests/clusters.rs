extern crate tree_child;

use tree_child::clusters;
use tree_child::newick;
use tree_child::tree_child_sequence;
use tree_child::tree::TreeBuilder;

/// Test that we find the right tree-child sequence with and without clustering
#[test]
fn clusters() {
    let mut builder = TreeBuilder::new();
    let newick      = "((a,((b,c),d)),e);\n((a,(b,(c,d))),e);\n(a,((b,(c,d)),e));\n";
    newick::parse_forest(&mut builder, newick).unwrap();
    let trees       = builder.trees();
    let seq         = tree_child_sequence::tree_child_sequence(trees.clone(), false, false);

    let clusters     = clusters::partition(trees);
    assert_eq!(clusters.len(), 2);
    let cluster_seqs = clusters.into_iter().map(
        |cluster| tree_child_sequence::tree_child_sequence(cluster, false, false)).collect();
    let cseq         = clusters::combine_tc_seqs(cluster_seqs);
    assert_eq!(seq, cseq);
}
