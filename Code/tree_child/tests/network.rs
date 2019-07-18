extern crate tree_child;

use tree_child::network::TcNet;
use tree_child::newick;
use tree_child::tree_child_sequence;
use tree_child::tree::TreeBuilder;

/// Test that we correctly construct a network if all trees are the same
#[test]
fn trivial_network() {
    let mut builder    = TreeBuilder::new();
    let tree_newick    = "(((a,b),(c,d)),(e,f));\n(((a,b),(c,d)),(e,f));\n(((a,b),(c,d)),(e,f));\n";
    newick::parse_forest(&mut builder, tree_newick).unwrap();
    let trees          = builder.trees();
    let seq            = tree_child_sequence::tree_child_sequence(
        trees.clone(), 32, Some(1), true, true);
    let network        = TcNet::from_seq(seq);
    let network_newick = newick::format_network(&network).unwrap();

    assert_eq!(network_newick, "(((a,b),(c,d)),(e,f));");
}

/// Test that we correctly construct a simple network with one reticulation
#[test]
fn simple_network_one_reticulation() {
    let mut builder    = TreeBuilder::new();
    let tree_newick    = "((a,b),c);\n(a,(b,c));\n";
    newick::parse_forest(&mut builder, tree_newick).unwrap();
    let trees          = builder.trees();
    let seq            = tree_child_sequence::tree_child_sequence(
        trees.clone(), 32, Some(1), true, true);
    let network        = TcNet::from_seq(seq);
    let network_newick = newick::format_network(&network).unwrap();

    assert_eq!(network_newick, "((a)#H0,((#H0,b),c));");
}

/// Test that we correctly construct a more complex network with three reticulations
#[test]
fn complex_network_three_reticulations() {
    let mut builder    = TreeBuilder::new();
    let tree_newick    =
    "(((a,c),d),((b,f),((g,e),h)));\n((a,(d,c)),(((e,g),(h,f)),b));\n((((h,(f,((g,e),c))),b),a),d);\n";
    newick::parse_forest(&mut builder, tree_newick).unwrap();
    let trees          = builder.trees();
    let seq            = tree_child_sequence::tree_child_sequence(
        trees.clone(), 1, None, true, true);
    let network        = TcNet::from_seq(seq);
    let network_newick = newick::format_network(&network).unwrap();

    assert_eq!(network_newick, "((#H0,(((#H0,c))#H1,d)),((a)#H0,((#H2,b),((#H2,(#H1,(g,e))),((f)#H2,h)))));");
}
