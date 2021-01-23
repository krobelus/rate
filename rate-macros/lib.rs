//! Internal macros for rate

extern crate proc_macro;
extern crate proc_macro2;

use quote::quote;

/// Default implementation of [HeapSpace](../rate_common/memory/trait.HeapSpace.html).
/// Use by adding `#[derive(HeapSpace)]` to your struct.
#[proc_macro_derive(HeapSpace)]
pub fn heap_space(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let type_name = ast.ident;
    let (impl_generics, type_generics, where_clause) = ast.generics.split_for_impl();
    let block = match ast.data {
        syn::Data::Struct(ref data_struct) => data_struct
            .fields
            .iter()
            .map(|field| {
                let field_name = &field.ident;
                quote!(self.#field_name.heap_space())
            })
            .fold(quote!(0), |a, b| quote!(#a + #b)),
        syn::Data::Enum(ref data_enum) => data_enum
            .variants
            .iter()
            .map(|field| quote!(self.#field.ident.heap_space()))
            .fold(quote!(0), |a, b| quote!(#a + #b)),
        syn::Data::Union(ref _data_union) => panic!("not implemented for unions"),
    };
    let implementation = quote!(
        impl #impl_generics
        HeapSpace for #type_name #type_generics #where_clause {
            fn heap_space(&self) -> usize {
                #block
            }
        }
    );
    implementation.into()
}
