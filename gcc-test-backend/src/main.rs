fn main() {
    const OPTION: Option<usize> = Some(32);

    const REF: Option<&usize> = OPTION.as_ref();
    assert_eq!(REF, Some(&32));

    const IS_SOME: bool = OPTION.is_some();
    assert!(IS_SOME);

    const IS_NONE: bool = OPTION.is_none();
    assert!(!IS_NONE);
}
